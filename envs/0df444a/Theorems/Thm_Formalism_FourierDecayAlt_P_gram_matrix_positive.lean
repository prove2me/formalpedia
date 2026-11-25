-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_gram_matrix_positive
-- name    : Formalism.FourierDecayAlt.P.gram_matrix_positive
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:31:22.383207+00:00
-- url     : https://prove2.me/theorems/b5e861b3-eed0-5ffe-a34c-ce244a35e170
-- title:
--   P: gram matrix positive
-- statement:
--   The P construction uses the gram matrix positive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GramProductIdentities.lean#L326-L326
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GramProductIdentities.lean#L326-L326

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

theorem Formalism.FourierDecayAlt.P.gram_matrix_positive : Formalism.FourierDecayAlt.FormPairingAction.GramPos := by sorry
