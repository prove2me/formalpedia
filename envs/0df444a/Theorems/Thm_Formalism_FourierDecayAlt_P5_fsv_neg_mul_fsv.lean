-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P5_fsv_neg_mul_fsv
-- name    : Formalism.FourierDecayAlt.P5.fsv_neg_mul_fsv
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T15:27:25.381229+00:00
-- url     : https://prove2.me/theorems/c01ca063-5ece-42ff-9b04-7295573b765c
-- title:
--   P5: fsv neg mul fsv
-- statement:
--   The P5 construction uses the fsv neg mul fsv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FsvMulFsvNeg.lean#L20-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FsvMulFsvNeg.lean#L20-L22

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

theorem Formalism.FourierDecayAlt.P5.fsv_neg_mul_fsv (s t : ℂ) : fsv (-s) t * fsv s t = 1 := by sorry
