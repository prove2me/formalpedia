-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LEx1_weighted_L2_zero
-- name    : Formalism.FourierDecayAlt.P.LEx1.weighted_L2_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:53:36.092639+00:00
-- url     : https://prove2.me/theorems/b34787d7-b899-44c0-824a-55c08c7f0cb8
-- title:
--   LEx1: weighted L2 zero
-- statement:
--   The LEx1 construction uses the weighted L2 zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedL2ConstMul.lean#L8-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedL2ConstMul.lean#L8-L11

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

theorem Formalism.FourierDecayAlt.P.LEx1.weighted_L2_zero (B : Base) (wt : B.Ω → ℝ) : WeightedL2 B wt (fun _ => 0) := by sorry
