-- Prove2me | solution 1 for polynomialSupNorm_le_add_of_uniform_approximation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:52:08.245973+00:00
-- url     : https://prove2.me/submissions/e25534f3-2e1e-4b1b-a756-286d9ba4fe9b

import Definitions.Def_Operator_Crouzeix_PolynomialSupNormZero
import Definitions.Def_Operator_Crouzeix_PolynomialCompanionNormalization

set_option autoImplicit false
open Filter
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
theorem _root_.solution
    (r : Polynomial ℂ) (S : Set ℂ) (g : ℂ → ℂ) (m ε : ℝ)
    (hm : 0 ≤ m) (hε : 0 ≤ ε)
    (hg : ∀ z ∈ S, ‖g z‖ ≤ m)
    (happrox : ∀ z ∈ S, ‖Polynomial.eval z r - g z‖ ≤ ε) :
    polynomialSupNorm r S ≤ m + ε := by
  unfold polynomialSupNorm
  refine Real.iSup_le (fun z ↦ ?_) (add_nonneg hm hε)
  refine Real.iSup_le (fun hz ↦ ?_) (add_nonneg hm hε)
  calc
    ‖Polynomial.eval z r‖ =
        ‖(Polynomial.eval z r - g z) + g z‖ := by rw [sub_add_cancel]
    _ ≤ ‖Polynomial.eval z r - g z‖ + ‖g z‖ := norm_add_le _ _
    _ ≤ ε + m := add_le_add (happrox z hz) (hg z hz)
    _ = m + ε := add_comm _ _
