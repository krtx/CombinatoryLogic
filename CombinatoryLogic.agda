module CombinatoryLogic where

open import Confluence
open import Data.Nat
open import Data.Star using (Star; ε; _◅_; _◅◅_)
open import Data.Product
  using (_,_; ∃; _×_; proj₁; proj₂)
  renaming (map to ×-map; swap to ×-swap)
open import Function using (id; _$_)

infixl 6 _∘_

data 𝐶 : Set where
  var : ℕ → 𝐶
  K   : 𝐶
  S   : 𝐶
  _∘_ : 𝐶 → 𝐶 → 𝐶

infix 4 _▻_  -- weak reduction
infix 4 _▻⋆_ -- reflexive transitive closure of weak reduction
infix 4 _►_  -- weak parallel reduction
infix 4 _►⋆_ -- reflexive transitive closure of weak parallel reduction

-- weak reduction
data _▻_ : 𝐶 → 𝐶 → Set where
  w-K    : ∀ {f g} → K ∘ f ∘ g ▻ f
  w-S    : ∀ {f g h} → S ∘ f ∘ g ∘ h ▻ f ∘ h ∘ (g ∘ h)
  w-left : ∀ {f f′ g} → f ▻ f′ → f ∘ g ▻ f′ ∘ g
  w-righ : ∀ {f g g′} → g ▻ g′ → f ∘ g ▻ f ∘ g′

-- reflexive transitive closure of weak reduction
_▻⋆_ : 𝐶 → 𝐶 → Set
_▻⋆_ = Star _▻_

-- parallel reduction of weak reduction
data _►_ : 𝐶 → 𝐶 → Set where
  p-refl : ∀ {f}
           → f ► f
  p-K    : ∀ {f f′ g}
           → f ► f′
           → K ∘ f ∘ g ► f′
  p-S    : ∀ {f f′ g g′ h h′}
           → f ► f′
           → g ► g′
           → h ► h′
           → S ∘ f ∘ g ∘ h ► f′ ∘ h′ ∘ (g′ ∘ h′)
  p-app  : ∀ {f f′ g g′}
           → f ► f′
           → g ► g′
           → f ∘ g ► f′ ∘ g′

-- reflexive transitive closure of weak parallel reduction
_►⋆_ : 𝐶 → 𝐶 → Set
_►⋆_ = Star _►_

strip-K : ∀ {f f′} → K ∘ f ► K ∘ f′ → f ► f′
strip-K p-refl      = p-refl
strip-K (p-app _ r) = r

strip-S : ∀ {f f′ g g′} → S ∘ f ∘ g ► S ∘ f′ ∘ g′ → f ► f′ × g ► g′
strip-S p-refl                  = p-refl , p-refl
strip-S (p-app p-refl       r)  = p-refl , r
strip-S (p-app (p-app _ r₁) r₂) = r₁     , r₂

►-diamond : Diamond _►_

►-diamond-app-K : ∀ {f f₁ f₂ g g₁}
                  → (r₁ : K ∘ f ► K ∘ f₁) → (r₂ : g ► g₁) -- p-app
                  → (r₃ : f ► f₂)                         -- p-K
                  → ∃ λ h → (K ∘ f₁ ∘ g₁ ► h) × (f₂ ► h)
►-diamond-app-K r₁ r₂ r₃ =
  proj₁ h-cf , p-K (proj₁ (proj₂ h-cf)) , proj₂ (proj₂ h-cf)
  where
    h-cf = ►-diamond (strip-K r₁) r₃

►-diamond-app-S : ∀ {f f₁ f₂ g g₁ g₂ h h₁ h₂}
                  → (r₁ : S ∘ f ∘ g ► S ∘ f₁ ∘ g₁) → (r₂ : h ► h₁) -- p-app
                  → (r₃ : f ► f₂) → (r₄ : g ► g₂) → (r₅ : h ► h₂)  -- p-S
                  → ∃ λ i → (S ∘ f₁ ∘ g₁ ∘ h₁ ► i) × (f₂ ∘ h₂ ∘ (g₂ ∘ h₂) ► i)
►-diamond-app-S r₁ r₂ r₃ r₄ r₅ =
  f′ ∘ h′ ∘ (g′ ∘ h′) ,
  p-S (proj₁ f-cf) (proj₁ g-cf) (proj₁ h-cf) ,
  p-app (p-app (proj₂ f-cf) (proj₂ h-cf)) (p-app (proj₂ g-cf) (proj₂ h-cf))
  where
    f′ = proj₁ $ ►-diamond (proj₁ $ strip-S r₁) r₃
    g′ = proj₁ $ ►-diamond (proj₂ $ strip-S r₁) r₄
    h′ = proj₁ $ ►-diamond r₂ r₅
    f-cf = proj₂ $ ►-diamond (proj₁ $ strip-S r₁) r₃
    g-cf = proj₂ $ ►-diamond (proj₂ $ strip-S r₁) r₄
    h-cf = proj₂ $ ►-diamond r₂ r₅

►-diamond-S-S : ∀ {f f₁ f₂ g g₁ g₂ h h₁ h₂}
                → f ► f₁ → g ► g₁ → h ► h₁ -- p-S
                → f ► f₂ → g ► g₂ → h ► h₂ -- p-S
                → ∃ λ i → f₁ ∘ h₁ ∘ (g₁ ∘ h₁) ► i × f₂ ∘ h₂ ∘ (g₂ ∘ h₂) ► i
►-diamond-S-S r₁ r₂ r₃ r₄ r₅ r₆ =
  f′ ∘ h′ ∘ (g′ ∘ h′) ,
  p-app (p-app (proj₁ f-cf) (proj₁ h-cf)) (p-app (proj₁ g-cf) (proj₁ h-cf)) ,
  p-app (p-app (proj₂ f-cf) (proj₂ h-cf)) (p-app (proj₂ g-cf) (proj₂ h-cf))
  where
    f′ = proj₁ (►-diamond r₁ r₄)
    g′ = proj₁ (►-diamond r₂ r₅)
    h′ = proj₁ (►-diamond r₃ r₆)
    f-cf = proj₂ (►-diamond r₁ r₄)
    g-cf = proj₂ (►-diamond r₂ r₅)
    h-cf = proj₂ (►-diamond r₃ r₆)

►-diamond-app-app : ∀ {f f₁ f₂ g g₁ g₂}
                    → f ► f₁ → g ► g₁
                    → f ► f₂ → g ► g₂
                    → ∃ λ h → f₁ ∘ g₁ ► h × f₂ ∘ g₂ ► h
►-diamond-app-app r₁ r₂ r₃ r₄ =
  f′ ∘ g′ ,
  p-app (proj₁ f-cf) (proj₁ g-cf) , p-app (proj₂ f-cf) (proj₂ g-cf)
  where
    f′ = proj₁ (►-diamond r₁ r₃)
    g′ = proj₁ (►-diamond r₂ r₄)
    f-cf = proj₂ (►-diamond r₁ r₃)
    g-cf = proj₂ (►-diamond r₂ r₄)

►-diamond {f} {f₁} {.f} r      p-refl = f₁ , (p-refl , r)
►-diamond {f} {.f} {f₂} p-refl r      = f₂ , (r , p-refl)
►-diamond (p-K r₁) (p-K r₂) = ►-diamond r₁ r₂
►-diamond (p-K _)  (p-app {f′ = var x}     ()           _)
►-diamond (p-K _)  (p-app {f′ = K}         ()           _)
►-diamond (p-K _)  (p-app {f′ = S}         ()           _)
►-diamond (p-K _)  (p-app {f′ = var _ ∘ _} (p-app () _) _)
►-diamond (p-K _)  (p-app {f′ = S ∘ _}     (p-app () _) _)
►-diamond (p-K _)  (p-app {f′ = _ ∘ _ ∘ _} (p-app () _) _)
►-diamond (p-K r₁) (p-app {f′ = K ∘ _}     r₂          r₃) = ×-map id ×-swap $ ►-diamond-app-K r₂ r₃ r₁
►-diamond (p-app {f′ = var x}     ()          _)  (p-K _)
►-diamond (p-app {f′ = K}         ()          _)  (p-K _)
►-diamond (p-app {f′ = S}         ()          _)  (p-K _)
►-diamond (p-app {f′ = var _ ∘ _} (p-app () _) _) (p-K _)
►-diamond (p-app {f′ = S ∘ _}     (p-app () _) _) (p-K _)
►-diamond (p-app {f′ = _ ∘ _ ∘ _} (p-app () _) _) (p-K _)
►-diamond (p-app {f′ = K ∘ _}     r₁          r₂) (p-K r₃) = ►-diamond-app-K r₁ r₂ r₃
►-diamond (p-S r₁ r₂ r₃) (p-S r₄ r₅ r₆) = ►-diamond-S-S r₁ r₂ r₃ r₄ r₅ r₆
►-diamond (p-app r₁ r₂) (p-app r₃ r₄) = ►-diamond-app-app r₁ r₂ r₃ r₄ 
►-diamond (p-app {f′ = var _}         ()                     _) (p-S _ _ _)
►-diamond (p-app {f′ = K}             ()                     _) (p-S _ _ _)
►-diamond (p-app {f′ = S}             ()                     _) (p-S _ _ _)
►-diamond (p-app {f′ = var _ ∘ _}     (p-app ()           _) _) (p-S _ _ _)
►-diamond (p-app {f′ = K ∘ _}         (p-app ()           _) _) (p-S _ _ _)
►-diamond (p-app {f′ = S ∘ _}         (p-app ()           _) _) (p-S _ _ _)
►-diamond (p-app {f′ = var _ ∘ _ ∘ _} (p-app (p-app () _) _) _) (p-S _ _ _)
►-diamond (p-app {f′ = K ∘ _ ∘ _}     (p-app (p-app () _) _) _) (p-S _ _ _)
►-diamond (p-app {f′ = S ∘ _ ∘ _} r₁ r₂) (p-S r₃ r₄ r₅) = ►-diamond-app-S r₁ r₂ r₃ r₄ r₅
►-diamond (p-app {f′ = _ ∘ _ ∘ _ ∘ _} (p-app (p-app () _) _) _) (p-S _ _ _)
►-diamond (p-S _ _ _) (p-app {f′ = var _}         ()                     _)
►-diamond (p-S _ _ _) (p-app {f′ = K}             ()                     _)
►-diamond (p-S _ _ _) (p-app {f′ = S}             ()                     _)
►-diamond (p-S _ _ _) (p-app {f′ = var _ ∘ _}     (p-app ()           _) _)
►-diamond (p-S _ _ _) (p-app {f′ = K ∘ _}         (p-app ()           _) _)
►-diamond (p-S _ _ _) (p-app {f′ = S ∘ _}         (p-app ()           _) _)
►-diamond (p-S _ _ _) (p-app {f′ = var _ ∘ _ ∘ _} (p-app (p-app () _) _) _)
►-diamond (p-S _ _ _) (p-app {f′ = K ∘ _ ∘ _}     (p-app (p-app () _) _) _)
►-diamond (p-S r₃ r₄ r₅) (p-app {f′ = S ∘ _ ∘ _} r₁ r₂) = ×-map id ×-swap $ ►-diamond-app-S r₁ r₂ r₃ r₄ r₅
►-diamond (p-S _ _ _) (p-app {f′ = _ ∘ _ ∘ _ ∘ _} (p-app (p-app () _) _) _)

►⋆-diamond : Diamond _►⋆_
►⋆-diamond = strip-lemma ►-diamond

w-left⋆ : ∀ {f f′ g} → f ▻⋆ f′ → f ∘ g ▻⋆ f′ ∘ g
w-left⋆ ε = ε
w-left⋆ (r ◅ s) = w-left r ◅ w-left⋆ s

w-righ⋆ : ∀ {f f′ g} → f ▻⋆ f′ → g ∘ f ▻⋆ g ∘ f′
w-righ⋆ ε = ε
w-righ⋆ (r ◅ s) = w-righ r ◅ w-righ⋆ s

►⇒▻⋆ : ∀ {f g} → f ► g → f ▻⋆ g
►⇒▻⋆ p-refl = ε
►⇒▻⋆ (p-K r) = w-K ◅ ►⇒▻⋆ r
►⇒▻⋆ (p-S r₁ r₂ r₃) = w-S ◅ w-left⋆ (w-left⋆ (►⇒▻⋆ r₁))
                          ◅◅ w-left⋆ (w-righ⋆ (►⇒▻⋆ r₃))
                          ◅◅ w-righ⋆ (w-left⋆ (►⇒▻⋆ r₂))
                          ◅◅ w-righ⋆ (w-righ⋆ (►⇒▻⋆ r₃))
►⇒▻⋆ (p-app r₁ r₂) = w-left⋆ (►⇒▻⋆ r₁) ◅◅ w-righ⋆ (►⇒▻⋆ r₂)

▻⇒► : ∀ {f g} → f ▻ g → f ► g
▻⇒► w-K = p-K p-refl
▻⇒► w-S = p-S p-refl p-refl p-refl
▻⇒► (w-left r) = p-app (▻⇒► r) p-refl
▻⇒► (w-righ r) = p-app p-refl (▻⇒► r)

►⋆⇒▻⋆ : ∀ {f g} → f ►⋆ g → f ▻⋆ g
►⋆⇒▻⋆ ε = ε
►⋆⇒▻⋆ (p-refl ◅ s) = ►⋆⇒▻⋆ s
►⋆⇒▻⋆ (p-K r ◅ s) = w-K ◅ ►⇒▻⋆ r ◅◅ ►⋆⇒▻⋆ s
►⋆⇒▻⋆ (p-S r₁ r₂ r₃ ◅ s) = w-S ◅ w-left⋆ (w-left⋆ (►⇒▻⋆ r₁))
                               ◅◅ w-left⋆ (w-righ⋆ (►⇒▻⋆ r₃))
                               ◅◅ w-righ⋆ (w-left⋆ (►⇒▻⋆ r₂))
                               ◅◅ w-righ⋆ (w-righ⋆ (►⇒▻⋆ r₃))
                               ◅◅ ►⋆⇒▻⋆ s
►⋆⇒▻⋆ (p-app r₁ r₂ ◅ s) = w-left⋆ (►⇒▻⋆ r₁)
                          ◅◅ w-righ⋆ (►⇒▻⋆ r₂)
                          ◅◅ ►⋆⇒▻⋆ s

▻⋆⇒►⋆ : ∀ {f g} → f ▻⋆ g → f ►⋆ g
▻⋆⇒►⋆ ε = ε
▻⋆⇒►⋆ (w-K ◅ s) = p-K p-refl ◅ ▻⋆⇒►⋆ s
▻⋆⇒►⋆ (w-S ◅ s) = p-S p-refl p-refl p-refl ◅ ▻⋆⇒►⋆ s
▻⋆⇒►⋆ (w-left r ◅ s) = p-app (▻⇒► r) p-refl ◅ ▻⋆⇒►⋆ s
▻⋆⇒►⋆ (w-righ r ◅ s) = p-app p-refl (▻⇒► r) ◅ ▻⋆⇒►⋆ s

▻⋆-diamond : Diamond _▻⋆_
▻⋆-diamond r₁ r₂ = proj₁ ►-cf , ►⋆⇒▻⋆ (proj₁ (proj₂ ►-cf))
                              , ►⋆⇒▻⋆ (proj₂ (proj₂ ►-cf))
  where
    ►-cf = ►⋆-diamond (▻⋆⇒►⋆ r₁) (▻⋆⇒►⋆ r₂)

▻-CR : Church-Rosser _▻_
▻-CR = ▻⋆-diamond
