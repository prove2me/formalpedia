-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P5_fsv_mul_fsv_neg
-- name    : Formalism.FourierDecayAlt.P5.fsv_mul_fsv_neg
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T15:25:07.086401+00:00
-- url     : https://prove2.me/theorems/c9164b9c-8f3f-4460-9d82-73a34e3d3a39
-- title:
--   P5: fsv mul fsv neg
-- statement:
--   The P5 construction uses the fsv mul fsv neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FsvMulFsvNeg.lean#L14-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FsvMulFsvNeg.lean#L14-L18

import Definitions.Def_Formalism_HermitianCurvature_CompositeFormulaLevelZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FsvMulFsvNeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexConjugate ContDiff
open Filter Topology
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd

theorem Formalism.FourierDecayAlt.P5.fsv_mul_fsv_neg (s t : ℂ) : fsv s t * fsv (-s) t = 1 := by sorry
