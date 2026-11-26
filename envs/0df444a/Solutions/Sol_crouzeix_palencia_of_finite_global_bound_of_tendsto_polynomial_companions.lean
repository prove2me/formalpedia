-- Prove2me | solution 1 for crouzeix_palencia_of_finite_global_bound_of_tendsto_polynomial_companions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:20:24.237509+00:00
-- url     : https://prove2.me/submissions/1844ff03-9750-43c7-8640-6f304bb3d6d3

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_SpectralSet_Normal
import Definitions.Def_Operator_Crouzeix_Palencia
import Theorems.Thm_isKPolynomialSpectralSet_of_finite_global_bound_of_tendsto_polynomial_companions
import Theorems.Thm_norm_le_of_mem_numericalRange
import Theorems.Thm_spectrum_subset_closure_numericalRange

section
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
private theorem isCompact_closure_numericalRange_palencia (A : E →L[ℂ] E) :
    IsCompact (closure (numericalRange A)) := by
  have hbounded : Bornology.IsBounded (numericalRange A) :=
    Metric.isBounded_closedBall.subset (fun z hz => by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact norm_le_of_mem_numericalRange A hz)
  exact hbounded.isCompact_closure
variable [CompleteSpace E]
end

set_option autoImplicit false
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E)
    (hfinite : ∃ K : ℝ, 0 ≤ K ∧ ∀ p : Polynomial ℂ,
      ‖Polynomial.aeval A p‖ ≤
        K * polynomialSupNorm p (closure (numericalRange A)))
    (hcompanion : ∀ p : Polynomial ℂ,
      ∃ (G : E →L[ℂ] E) (q : ℕ → Polynomial ℂ),
        (∀ n, polynomialSupNorm (q n) (closure (numericalRange A)) ≤
          polynomialSupNorm p (closure (numericalRange A))) ∧
        Filter.Tendsto (fun n ↦ Polynomial.aeval A (q n)) Filter.atTop
          (nhds G) ∧
        ‖Polynomial.aeval A p + star G‖ ≤
          2 * polynomialSupNorm p (closure (numericalRange A))) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  exact
    isKPolynomialSpectralSet_of_finite_global_bound_of_tendsto_polynomial_companions
      A (closure (numericalRange A))
        (isCompact_closure_numericalRange_palencia A)
        (spectrum_subset_closure_numericalRange A) hfinite hcompanion
