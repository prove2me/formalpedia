-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Fr3_eeConj_abs
-- name    : Formalism.FourierDecayAlt.P.Fr3.eeConj_abs
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T13:00:41.177298+00:00
-- url     : https://prove2.me/theorems/12081f4a-0f24-48f1-b113-1ecd20eafee8
-- title:
--   Fr3: ee Conj abs
-- statement:
--   The Fr3 construction uses the ee Conj abs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/L0ConstantPartCommute.lean#L108-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/L0ConstantPartCommute.lean#L108-L136

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleGD
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleSS
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_L0ConstantPartCommute
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr3

theorem Formalism.FourierDecayAlt.P.Fr3.eeConj_abs {B : Type} [Ring B] (G Gi x xi l0 z κ κi e D : B)
    (hG : Gi * G = 1) (hκ : κi * κ = 1) (hx : xi * x = 1)
    (c1 : l0 * G = G * (l0 - z)) (cxl : Commute x l0) (cxz : Commute x z) (cxκ : Commute x κ)
    (cκG : Commute κ G) (ceG : Commute e G)
    (h : G * x * (l0 + κ * e) - (l0 + κ * e) * (G * x) = -(G * x * (-z + κ * D))) :
    xi * e * x - D = e := by sorry
