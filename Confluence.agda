module Confluence where

open import Data.Star
open import Data.Product

Diamond : ∀ {A} → (A → A → Set) → Set
Diamond R = ∀ {f f₁ f₂} → R f f₁ → R f f₂ → ∃ λ g → R f₁ g × R f₂ g

Church-Rosser : ∀ {A} → (A → A → Set) → Set
Church-Rosser R = Diamond (Star R)

strip-lemma-1 : ∀ {A} → {R : A → A → Set} → Diamond R
                → ∀ {F F₁ F₂} → R F F₁ → Star R F F₂
                → ∃ λ G → Star R F₁ G × R F₂ G
strip-lemma-1 DiaR {F} {F₁} {.F} r₁ ε = F₁ , ε , r₁
strip-lemma-1 {A} {R} DiaR {F} {F₁} {F₂} r₁ (_◅_ {j = j} x r₂) = c
  where
    --  F  → j  -*→ F₂
    --  ↓    ↓      ↓
    --  F₁ → Gₐ -*→ Gₑ
    --
    --   DiaR  induction
    --         hypothesis
    a : ∃ λ G → R F₁ G × R j G
    a = DiaR r₁ x

    e : ∃ λ G → Star R (proj₁ a) G × R F₂ G
    e = strip-lemma-1 DiaR (proj₂ (proj₂ a)) r₂

    c : ∃ λ G → Star R F₁ G × R F₂ G
    c = proj₁ e , proj₁ (proj₂ a) ◅ proj₁ (proj₂ e) , proj₂ (proj₂ e)

strip-lemma : ∀ {A} → {R : A → A → Set} → Diamond R → Diamond (Star R)
strip-lemma DiaR {F} {.F} {F₂} ε r = F₂ , r , ε
strip-lemma {A} {R} DiaR {F} {F₁} {F₂} (_◅_ {j = j} x r₁) r₂ = c
  where
    -- 
    --  F  -*→  F₂
    --  ↓       ↓     strip-lemma-1
    --  j  -*→  Gₐ
    --  |       |
    --  *       *     induction hypothesis
    --  ↓       ↓
    --  F₁ -*→  Gₑ
    --
    a : ∃ λ G → Star R j G × R F₂ G
    a = strip-lemma-1 DiaR x r₂

    e : ∃ λ G → Star R F₁ G × Star R (proj₁ a) G
    e = strip-lemma DiaR r₁ (proj₁ (proj₂ a))

    c : ∃ λ G → Star R F₁ G × Star R F₂ G
    c = proj₁ e , proj₁ (proj₂ e) , proj₂ (proj₂ a) ◅ proj₂ (proj₂ e)
