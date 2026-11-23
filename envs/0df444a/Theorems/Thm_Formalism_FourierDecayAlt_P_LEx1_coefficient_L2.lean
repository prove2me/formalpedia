-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LEx1_coefficient_L2
-- name    : Formalism.FourierDecayAlt.P.LEx1.coefficient_L2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:18:34.686524+00:00
-- url     : https://prove2.me/theorems/e74f7e35-efe8-4190-b2c7-2bdc147a0ccf
-- title:
--   LEx1: coefficient L2
-- statement:
--   The LEx1 construction uses the coefficient L2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedL2ConstMul.lean#L114-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedL2ConstMul.lean#L114-L128

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StepClaimFromStepsFull
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedL2ConstMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx1
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate

theorem Formalism.FourierDecayAlt.P.LEx1.coefficient_L2 : InterpolationCoefficientsInL2 := by sorry
