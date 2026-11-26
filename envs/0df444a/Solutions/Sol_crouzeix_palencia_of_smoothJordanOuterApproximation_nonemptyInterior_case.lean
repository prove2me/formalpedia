-- Prove2me | solution 1 for crouzeix_palencia_of_smoothJordanOuterApproximation_nonemptyInterior_case
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:39:53.856295+00:00
-- url     : https://prove2.me/submissions/074e8bda-354f-400d-8267-300a1c6aae30

import Definitions.Def_Operator_Crouzeix_SmoothJordanOuterApproximation
import Definitions.Def_Operator_Crouzeix_SmoothJordanOuterApproximationReduction
import Theorems.Thm_hasSmoothJordanOuterApproximation_of_nonemptyInterior_case
import Theorems.Thm_convex_numericalRange
import Theorems.Thm_crouzeix_palencia_of_smoothJordanOuterApproximation
import Theorems.Thm_mem_numericalRange
import Theorems.Thm_norm_le_of_mem_numericalRange
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open Complex Metric Set
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [Nontrivial E]
theorem _root_.solution
    (A : E →L[ℂ] E)
    (hfull : ∀ K : Set ℂ, IsCompact K → Convex ℝ K →
      (interior K).Nonempty → HasSmoothJordanOuterApproximation K) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  have hcompact : IsCompact (closure (numericalRange A)) := by
    have hbounded : Bornology.IsBounded (numericalRange A) :=
      Metric.isBounded_closedBall.subset (fun z hz => by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact norm_le_of_mem_numericalRange A hz)
    exact hbounded.isCompact_closure
  have hnonempty : (closure (numericalRange A)).Nonempty := by
    obtain ⟨x, hx⟩ : (Metric.sphere (0 : E) 1).Nonempty :=
      NormedSpace.sphere_nonempty.mpr zero_le_one
    have hxnorm : ‖x‖ = 1 := by
      rw [Metric.mem_sphere, dist_zero_right] at hx
      exact hx
    exact ⟨⟪x, A x⟫_ℂ,
      subset_closure ((mem_numericalRange A _).mpr ⟨x, hxnorm, rfl⟩)⟩
  apply crouzeix_palencia_of_smoothJordanOuterApproximation A
  exact hasSmoothJordanOuterApproximation_of_nonemptyInterior_case
    hcompact hnonempty (convex_numericalRange A).closure hfull
