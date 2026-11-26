-- Prove2me | solution 1 for crouzeix_palencia_of_antitone_compact_tendsto_polynomial_companions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:41:50.608809+00:00
-- url     : https://prove2.me/submissions/b23a8761-0aee-4ce5-82c2-8ac78b8e4931

import Definitions.Def_Operator_Crouzeix_ApproximationSupNorm
import Definitions.Def_Operator_Crouzeix_CompactThickeningApprox
import Definitions.Def_Operator_Crouzeix_PalenciaApproximation
import Definitions.Def_Operator_Crouzeix_PalenciaExhaustion
import Theorems.Thm_isKPolynomialSpectralSet_of_finite_global_bound_of_tendsto_polynomial_companions
import Theorems.Thm_spectrum_subset_closure_numericalRange
import Theorems.Thm_tendsto_polynomialSupNorm_atTop_of_antitone_isCompact


set_option autoImplicit false
open Filter Set
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (K : ℕ → Set ℂ)
    (hanti : Antitone K) (hcompact : ∀ n, IsCompact (K n))
    (hnonempty : ∀ n, (K n).Nonempty)
    (hinter : (⋂ n, K n) = closure (numericalRange A))
    (hfinite : ∀ n, ∃ C : ℝ, 0 ≤ C ∧ ∀ p : Polynomial ℂ,
      ‖Polynomial.aeval A p‖ ≤ C * polynomialSupNorm p (K n))
    (hcompanion : ∀ (p : Polynomial ℂ) (n : ℕ),
      ∃ (G : E →L[ℂ] E) (q : ℕ → Polynomial ℂ),
        (∀ j, polynomialSupNorm (q j) (K n) ≤
          polynomialSupNorm p (K n)) ∧
        Tendsto (fun j ↦ Polynomial.aeval A (q j)) atTop (nhds G) ∧
        ‖Polynomial.aeval A p + star G‖ ≤
          2 * polynomialSupNorm p (K n)) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  have hstage : ∀ n,
      IsKPolynomialSpectralSet A (1 + Real.sqrt 2) (K n) := by
    intro n
    apply
      isKPolynomialSpectralSet_of_finite_global_bound_of_tendsto_polynomial_companions
        A (K n) (hcompact n)
    · exact (spectrum_subset_closure_numericalRange A).trans (by
        rw [← hinter]
        exact iInter_subset K n)
    · exact hfinite n
    · intro p
      exact hcompanion p n
  constructor
  · exact spectrum_subset_closure_numericalRange A
  · intro p
    have hlim := tendsto_polynomialSupNorm_atTop_of_antitone_isCompact
      p K hanti hcompact hnonempty
    rw [hinter] at hlim
    exact le_of_tendsto_of_tendsto' tendsto_const_nhds
      (tendsto_const_nhds.mul hlim) (fun n ↦ (hstage n).2 p)
