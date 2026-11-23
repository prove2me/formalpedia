-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LEx1_absorb
-- name    : Formalism.FourierDecayAlt.P.LEx1.absorb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:51:44.244817+00:00
-- url     : https://prove2.me/theorems/86e75f95-d250-4f31-a504-eea617da28b6
-- title:
--   LEx1: absorb
-- statement:
--   The LEx1 construction uses the absorb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StepClaimFromStepsFull.lean#L118-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StepClaimFromStepsFull.lean#L118-L125

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaEprimeFromSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StepClaimFromStepsFull
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
noncomputable section

theorem Formalism.FourierDecayAlt.P.LEx1.absorb : Absorb := by sorry
