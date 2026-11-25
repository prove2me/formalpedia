-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_class_lower_decay_holds
-- name    : Formalism.FourierDecayAlt.P.CutMP.class_lower_decay_holds
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:40:18.262509+00:00
-- url     : https://prove2.me/theorems/63b19867-904f-5e06-ae08-c45fa1746d34
-- title:
--   Cut MP: class lower decay holds
-- statement:
--   The Cut MP construction uses the class lower decay holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutJDCCLower.lean#L13-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutJDCCLower.lean#L13-L41

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJD
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJDCCLower
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
open scoped ContDiff
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section

theorem Formalism.FourierDecayAlt.P.CutMP.class_lower_decay_holds : JDCCLower := by sorry
