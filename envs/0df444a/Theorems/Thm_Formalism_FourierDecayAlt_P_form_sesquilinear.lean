-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_form_sesquilinear
-- name    : Formalism.FourierDecayAlt.P.form_sesquilinear
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:31:53.18452+00:00
-- url     : https://prove2.me/theorems/0261edb2-da52-5088-865e-80575d5dc7e9
-- title:
--   P: form sesquilinear
-- statement:
--   The P construction uses the form sesquilinear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GramProductIdentities.lean#L324-L324
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GramProductIdentities.lean#L324-L324

import Definitions.Def_Formalism_HermitianCurvature_PositionExpansionTopCoefficients
import Definitions.Def_Lemmata_HermitianSesquilinear_ConjEqOfNonnegReal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramProductIdentities
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem Formalism.FourierDecayAlt.P.form_sesquilinear : Formalism.FourierDecayAlt.FormPairingAction.FormSesq := by sorry
