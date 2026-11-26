-- Prove2me | solution 1 for crouzeix_palencia_of_tendsto_auxiliary_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:37:02.173161+00:00
-- url     : https://prove2.me/submissions/97907af7-d2f2-47e0-b0ed-a844f2e2c85f

import Definitions.Def_Operator_Crouzeix_Palencia
import Definitions.Def_Operator_Crouzeix_PalenciaApproximation
import Theorems.Thm_norm_le_one_add_sqrt_two_mul_of_tendsto_auxiliary_bounds
import Theorems.Thm_spectrum_subset_closure_numericalRange


set_option autoImplicit false
open Filter
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E)
    (haux : ∀ p : Polynomial ℂ, ∃ M : ℕ → ℝ,
      Tendsto M atTop
          (nhds (polynomialSupNorm p (closure (numericalRange A)))) ∧
      ∀ n : ℕ, ∃ G : E →L[ℂ] E,
        ‖Polynomial.aeval A p + star G‖ ≤ 2 * M n ∧
        ‖Polynomial.aeval A p * G‖ ≤ (M n) ^ 2) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  constructor
  · exact spectrum_subset_closure_numericalRange A
  · intro p
    obtain ⟨M, hM, hstage⟩ := haux p
    exact norm_le_one_add_sqrt_two_mul_of_tendsto_auxiliary_bounds
      (Polynomial.aeval A p) M hM hstage
