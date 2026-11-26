-- Prove2me | solution 1 for exists_smoothJordanDomain_for_numericalRange
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:02:48.746606+00:00
-- url     : https://prove2.me/submissions/ba8288c9-92c2-4369-900e-1eeae93fc916

import Definitions.Def_Operator_Crouzeix_ContourIntegral
import Definitions.Def_Operator_Crouzeix_SmoothApprox
import Definitions.Def_Operator_NumericalRange_Bounded
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Definitions.Def_Operator_Crouzeix_AuxOperator
import Theorems.Thm_exists_smoothJordanDomain_superset_of_isCompact
import Theorems.Thm_norm_le_of_mem_numericalRange


set_option autoImplicit false
open Complex Set spectrum
open scoped InnerProductSpace Real Interval
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution (A : E →L[ℂ] E) :
    ∃ Omega : SmoothJordanDomain, closure (numericalRange A) ⊆ Omega.carrier := by
  have hbounded : Bornology.IsBounded (numericalRange A) :=
    Metric.isBounded_closedBall.subset (fun z hz => by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact norm_le_of_mem_numericalRange A hz)
  exact exists_smoothJordanDomain_superset_of_isCompact _ hbounded.isCompact_closure
