-- Prove2me | Theorems.Thm_AggNash_Existence_proposition_2_3
-- name    : AggNash.Existence.proposition_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:37:09.501815+00:00
-- url     : https://prove2.me/theorems/281d8d98-1b18-4f68-8c90-2b3e15e22c1f
-- title:
--   Proposition 2.3, p. 5 — under Assumption 1 the convexified game Γ̃ admits a PNE
-- statement:
--   Work in the non-convex sum-aggregative game $\Gamma$ under the standing assumptions and Assumption 1 (see the Model definitions). The convexified game $\tilde\Gamma$, in which player $i$ chooses $x_i\in\tilde{\mathcal X}_i=\operatorname{conv}\mathcal X_i$ and pays the convexified cost $\tilde f_i$ of (2.2), admits a pure Nash equilibrium: there is $\tilde x\in\tilde{\mathcal X}$ with
--
--   $$
--   \tilde f_i(\tilde x_i,\tilde x_{-i})\le\tilde f_i(x_i,\tilde x_{-i})\qquad\text{for every player } i \text{ and every } x_i\in\tilde{\mathcal X}_i.
--   $$
--
--   This equilibrium is the starting point of the Shapley–Folkman disaggregation that produces an approximate equilibrium of the non-convex game (Proposition 2.4).
-- source:
--   Liu, Oudjane & Wan, Approximate Nash equilibria in large non-convex aggregative games, arXiv:2011.12604v3, p. 5, Proposition 2.3

import Mathlib
import Definitions.Def_AggNash_Existence_Model

namespace AggNash.Existence

/-- Proposition 2.3 (p. 5). Under Assumption 1, the convexified game `Γ̃` (action sets
`𝒳̃ᵢ = conv 𝒳ᵢ`, costs `f̃ᵢ` of (2.2)) admits a pure Nash equilibrium. -/
theorem proposition_2_3
    {n d q : ℕ} (X : Fin n → Set (E d)) (A : Fin n → (E d →L[ℝ] E q))
    (θ : Fin n → E d → E q → ℝ) (Ω : Set (E q)) (Δ M H γ : ℝ)
    (hstd : StandingHyp X A Ω Δ M) (hA1 : Assumption1 X Ω θ H γ) :
    ∃ x : Fin n → E d, IsEpsPNE (fun i => convexHull ℝ (X i)) (convCost X θ A) 0 x := by sorry

end AggNash.Existence
