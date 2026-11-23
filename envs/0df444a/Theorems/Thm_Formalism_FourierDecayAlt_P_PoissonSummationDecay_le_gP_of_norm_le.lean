-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PoissonSummationDecay_le_gP_of_norm_le
-- name    : Formalism.FourierDecayAlt.P.PoissonSummationDecay.le_gP_of_norm_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:20:36.502597+00:00
-- url     : https://prove2.me/theorems/fb0c38cf-cd5c-4c96-9395-7c5ffed61fa1
-- title:
--   Poisson Summation Decay: le g P of norm le
-- statement:
--   The Poisson Summation Decay construction uses the le g P of norm le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PoissonSummationDecay.lean#L142-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PoissonSummationDecay.lean#L142-L151

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
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ι : Type} [Fintype ι]

theorem Formalism.FourierDecayAlt.P.PoissonSummationDecay.le_gP_of_norm_le (π : ι → V →L[ℝ] ℂ) (R : ℝ) (x : V) (hx : ‖x‖ ≤ R) :
    ∏ v, ((1 + ‖π v‖ * R)^3)⁻¹ ≤ gP π x := by sorry
