-- Prove2me | solution 1 for crouzeix_palencia_of_compactThickening_tendsto_polynomial_companions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:42:43.970421+00:00
-- url     : https://prove2.me/submissions/c9965131-3583-42a7-a25d-39835701a69c

import Definitions.Def_Operator_Crouzeix_ApproximationSupNorm
import Definitions.Def_Operator_Crouzeix_CompactThickeningApprox
import Definitions.Def_Operator_Crouzeix_PalenciaApproximation
import Definitions.Def_Operator_Crouzeix_PalenciaExhaustion
import Theorems.Thm_crouzeix_palencia_of_antitone_compact_tendsto_polynomial_companions
import Theorems.Thm_compactThickeningApprox_spec
import Theorems.Thm_mem_numericalRange
import Theorems.Thm_norm_le_of_mem_numericalRange
import Theorems.Thm_polynomialSupNorm_nonneg
import Theorems.Thm_spectrum_subset_closure_numericalRange
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open Filter Set
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E)
    (hfinite : ∀ n, ∃ C : ℝ, 0 ≤ C ∧ ∀ p : Polynomial ℂ,
      ‖Polynomial.aeval A p‖ ≤ C * polynomialSupNorm p
        (compactThickeningApprox (closure (numericalRange A)) n))
    (hcompanion : ∀ (p : Polynomial ℂ) (n : ℕ),
      ∃ (G : E →L[ℂ] E) (q : ℕ → Polynomial ℂ),
        (∀ j, polynomialSupNorm (q j)
            (compactThickeningApprox (closure (numericalRange A)) n) ≤
          polynomialSupNorm p
            (compactThickeningApprox (closure (numericalRange A)) n)) ∧
        Tendsto (fun j ↦ Polynomial.aeval A (q j)) atTop (nhds G) ∧
        ‖Polynomial.aeval A p + star G‖ ≤ 2 * polynomialSupNorm p
          (compactThickeningApprox (closure (numericalRange A)) n)) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · let _ := hE
    constructor
    · exact spectrum_subset_closure_numericalRange A
    · intro p
      have hzero : Polynomial.aeval A p = 0 := Subsingleton.elim _ _
      rw [hzero, norm_zero]
      exact mul_nonneg (add_nonneg zero_le_one (Real.sqrt_nonneg 2))
        (polynomialSupNorm_nonneg p (closure (numericalRange A)))
  · let _ := hE
    have hcompact : IsCompact (closure (numericalRange A)) := by
      have hbounded : Bornology.IsBounded (numericalRange A) :=
        Metric.isBounded_closedBall.subset (fun z hz ↦ by
          rw [Metric.mem_closedBall, dist_zero_right]
          exact norm_le_of_mem_numericalRange A hz)
      exact hbounded.isCompact_closure
    have hnonempty : (closure (numericalRange A)).Nonempty := by
      obtain ⟨x, hx⟩ : (Metric.sphere (0 : E) 1).Nonempty :=
        NormedSpace.sphere_nonempty.mpr zero_le_one
      have hxnorm : ‖x‖ = 1 := by
        rw [Metric.mem_sphere, dist_zero_right] at hx
        exact hx
      have hW : (numericalRange A).Nonempty :=
        ⟨⟪x, A x⟫_ℂ, (mem_numericalRange A _).mpr ⟨x, hxnorm, rfl⟩⟩
      exact hW.mono subset_closure
    obtain ⟨hanti, hstageCompact, hstageNonempty, hinter⟩ :=
      compactThickeningApprox_spec (closure (numericalRange A)) hcompact hnonempty
    exact
      crouzeix_palencia_of_antitone_compact_tendsto_polynomial_companions
        A _ hanti hstageCompact hstageNonempty hinter hfinite hcompanion
