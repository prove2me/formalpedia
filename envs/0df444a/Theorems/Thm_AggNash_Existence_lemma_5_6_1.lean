-- Prove2me | Theorems.Thm_AggNash_Existence_lemma_5_6_1
-- name    : AggNash.Existence.lemma_5_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:37:26.776222+00:00
-- url     : https://prove2.me/theorems/75e14f6d-3397-48bf-bdca-c48f4c41fc78
-- title:
--   Lemma 5.6 (1), p. 19 — fᵢ = f̃ᵢ at every generator point
-- statement:
--   Work in the non-convex sum-aggregative game $\Gamma$ under the standing assumptions and Assumption 1, with $f_i$ the cost (2.1), $\tilde f_i$ the convexified cost (2.2), and generators as in Definition 2.2. For any profile $\tilde x\in\tilde{\mathcal X}$, any player $i$ and any generator $Z(i,\tilde x)$,
--
--   $$
--   f_i(x_i,\tilde x_{-i})=\tilde f_i(x_i,\tilde x_{-i})\qquad\text{for all } x_i\in Z(i,\tilde x).
--   $$
--
--   The convexified cost agrees with the original cost at the points used to represent $\tilde x_i$; this is what lets a deviation analysis in $\tilde\Gamma$ be transferred to $\Gamma$ (Theorem 2.7).
--
--   **Formalization Note** Generators are the positive-weight components of a minimizer of (2.2) (see the Model definitions); with zero-weight components the statement is false.
-- source:
--   Liu, Oudjane & Wan, Approximate Nash equilibria in large non-convex aggregative games, arXiv:2011.12604v3, p. 19, Lemma 5.6 (1)

import Mathlib
import Definitions.Def_AggNash_Existence_Model

namespace AggNash.Existence

/-- Lemma 5.6 (1) (p. 19). Under Assumption 1, for any profile `x̃ ∈ 𝒳̃`, any player `i` and
any generator `Z(i, x̃)`, `fᵢ(xᵢ, x̃₋ᵢ) = f̃ᵢ(xᵢ, x̃₋ᵢ)` for all `xᵢ ∈ Z(i, x̃)`. -/
theorem lemma_5_6_1
    {n d q : ℕ} (X : Fin n → Set (E d)) (A : Fin n → (E d →L[ℝ] E q))
    (θ : Fin n → E d → E q → ℝ) (Ω : Set (E q)) (Δ M H γ : ℝ)
    (hstd : StandingHyp X A Ω Δ M) (hA1 : Assumption1 X Ω θ H γ)
    (x : Fin n → E d) (hx : ∀ j, x j ∈ convexHull ℝ (X j)) (i : Fin n) (Z : Set (E d))
    (hZ : IsGenerator X θ A i x Z) (y : E d) (hy : y ∈ Z) :
    cost θ A i (Function.update x i y) = convCost X θ A i (Function.update x i y) := by sorry

end AggNash.Existence
