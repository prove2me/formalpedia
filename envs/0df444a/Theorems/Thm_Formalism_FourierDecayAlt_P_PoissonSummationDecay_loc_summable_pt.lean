-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PoissonSummationDecay_loc_summable_pt
-- name    : Formalism.FourierDecayAlt.P.PoissonSummationDecay.loc_summable_pt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:31:08.822005+00:00
-- url     : https://prove2.me/theorems/8be91263-0903-4777-ae17-a48c733d242a
-- title:
--   Poisson Summation Decay: loc summable pt
-- statement:
--   The Poisson Summation Decay construction uses the loc summable pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PoissonSummationDecay.lean#L45-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PoissonSummationDecay.lean#L45-L48

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_LatticeTheta_ThetaShiftInversion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PoissonSummationDecay
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PoissonSummationDecay
open Formalism.FourierDecayAlt.F7
open Finset Polynomial
open MeasureTheory Formalism.H
open scoped FourierTransform RealInnerProductSpace ENNReal
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
  [FiniteDimensional ℝ V]
omit [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V] [InnerProductSpace ℝ V]

theorem Formalism.FourierDecayAlt.P.PoissonSummationDecay.loc_summable_pt (Λ : Submodule ℤ V) (φ : V → ℂ) (h : LocSummable Λ φ) (x : V) :
    Summable (fun l : Λ => φ ((l:V) + x)) := by sorry
