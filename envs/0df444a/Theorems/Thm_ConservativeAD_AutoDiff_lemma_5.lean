-- Prove2me | Theorems.Thm_ConservativeAD_AutoDiff_lemma_5
-- name    : ConservativeAD.AutoDiff.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:40:11.523885+00:00
-- url     : https://prove2.me/theorems/bbe8b164-5fd2-4e45-bdda-332ffa111866
-- title:
--   Lemma 5 — the product of conservative mappings is a conservative mapping for the composition
-- statement:
--   Let $F_1:\mathbb R^n\to\mathbb R^m$ and $F_2:\mathbb R^m\to\mathbb R^l$ be locally Lipschitz, let $J_1:\mathbb R^n\rightrightarrows\mathbb R^{m\times n}$ be a conservative mapping for $F_1$ and $J_2:\mathbb R^m\rightrightarrows\mathbb R^{l\times m}$ a conservative mapping for $F_2$. Then the product mapping
--
--   $$
--   x\mapsto J_2(F_1(x))\cdot J_1(x)=\{V_2V_1 : V_2\in J_2(F_1(x)),\ V_1\in J_1(x)\}
--   $$
--
--   is a conservative mapping for $F_2\circ F_1$.
--
--   This is the chain rule of the conservative calculus, the step through which automatic differentiation composes the Jacobians of elementary operations.
--
--   **Formalization Note** The paper writes $J_2:\mathbb R^p\rightrightarrows\mathbb R^{l\times m}$; since $J_2$ is evaluated at $F_1(\gamma(t))\in\mathbb R^m$ in the proof, its domain is $\mathbb R^m$. The product mapping "$J_2\cdot J_1$" is read, as in the proof, as $J_2$ evaluated at $F_1(x)$ times $J_1$ evaluated at $x$.
-- source:
--   Bolte, Pauwels, Conservative set valued fields, automatic differentiation, stochastic gradient methods and deep learning, TSE Working Paper 1044 (October 2019), p. 13, Lemma 5

import Mathlib
import Definitions.Def_ConservativeAD_AutoDiff_ConservativeMap

namespace ConservativeAD.AutoDiff

/-- Lemma 5 (the product of conservative mappings is conservative), p. 13. For locally Lipschitz
`F₁ : ℝ^n → ℝ^m`, `F₂ : ℝ^m → ℝ^l`, a conservative mapping `J₁` for `F₁` and a conservative mapping
`J₂ : ℝ^m ⇒ ℝ^{l×m}` for `F₂`, the product mapping `x ↦ { V₂ V₁ : V₂ ∈ J₂(F₁ x), V₁ ∈ J₁ x }` is a
conservative mapping for `F₂ ∘ F₁`. -/
theorem lemma_5 {n m l : ℕ}
    (F₁ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (F₂ : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin l))
    (hF₁ : LocallyLipschitz F₁) (hF₂ : LocallyLipschitz F₂)
    (J₁ : EuclideanSpace ℝ (Fin n) → Set (Matrix (Fin m) (Fin n) ℝ))
    (J₂ : EuclideanSpace ℝ (Fin m) → Set (Matrix (Fin l) (Fin m) ℝ))
    (hJ₁ : IsConservativeMap F₁ J₁) (hJ₂ : IsConservativeMap F₂ J₂) :
    IsConservativeMap (F₂ ∘ F₁)
      (fun x => {V | ∃ V₂ ∈ J₂ (F₁ x), ∃ V₁ ∈ J₁ x, V = V₂ * V₁}) := by sorry

end ConservativeAD.AutoDiff
