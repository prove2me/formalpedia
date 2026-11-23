-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PoissonSummationDecay_gP_mul_le_gP_add
-- name    : Formalism.FourierDecayAlt.P.PoissonSummationDecay.gP_mul_le_gP_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:20:27.692664+00:00
-- url     : https://prove2.me/theorems/2da7f766-b1c5-49fc-bc1a-f06dd180ab2a
-- title:
--   Poisson Summation Decay: g P mul le g P add
-- statement:
--   The Poisson Summation Decay construction uses the g P mul le g P add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PoissonSummationDecay.lean#L131-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PoissonSummationDecay.lean#L131-L140

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

theorem Formalism.FourierDecayAlt.P.PoissonSummationDecay.gP_mul_le_gP_add (π : ι → V →L[ℝ] ℂ) (c u : V) : gP π c * gP π u ≤ gP π (c + u) := by sorry
