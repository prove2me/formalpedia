-- Prove2me | solution 1 for isKPolynomialSpectralSet_of_finite_global_bound_of_tendsto_polynomial_companions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:38:51.48252+00:00
-- url     : https://prove2.me/submissions/f86db42b-eb90-49ce-a071-5af8b92cc9cc

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_SpectralSet_Normal
import Definitions.Def_Operator_Crouzeix_Palencia
import Theorems.Thm_norm_fourth_power_le_of_tendsto_polynomial_companions
import Theorems.Thm_isKPolynomialSpectralSet_of_finite_global_bound_of_uniform_fourth_power_improvement
import Theorems.Thm_polynomialSupNorm_nonneg


set_option autoImplicit false
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (S : Set ℂ) (hS : IsCompact S)
    (hspectrum : spectrum ℂ A ⊆ S)
    (hfinite : ∃ K : ℝ, 0 ≤ K ∧ ∀ p : Polynomial ℂ,
      ‖Polynomial.aeval A p‖ ≤ K * polynomialSupNorm p S)
    (hcompanion : ∀ p : Polynomial ℂ,
      ∃ (G : E →L[ℂ] E) (q : ℕ → Polynomial ℂ),
        (∀ n, polynomialSupNorm (q n) S ≤ polynomialSupNorm p S) ∧
        Filter.Tendsto (fun n ↦ Polynomial.aeval A (q n)) Filter.atTop
          (nhds G) ∧
        ‖Polynomial.aeval A p + star G‖ ≤
          2 * polynomialSupNorm p S) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2) S := by
  apply
    isKPolynomialSpectralSet_of_finite_global_bound_of_uniform_fourth_power_improvement
      A S hspectrum hfinite
  intro K hK hcalc p
  obtain ⟨G, q, hq, hlim, hsymm⟩ := hcompanion p
  exact norm_fourth_power_le_of_tendsto_polynomial_companions
    A hK (polynomialSupNorm_nonneg p S) hS hcalc p le_rfl
      G q hq hlim hsymm
