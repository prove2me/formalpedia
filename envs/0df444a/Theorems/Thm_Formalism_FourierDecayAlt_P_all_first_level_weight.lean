-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_all_first_level_weight
-- name    : Formalism.FourierDecayAlt.P.all_first_level_weight
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:28:25.939684+00:00
-- url     : https://prove2.me/theorems/66be4f22-066c-429d-bb87-e54ecd164287
-- title:
--   P: all first level weight
-- statement:
--   The P construction uses the all first level weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ProductFactorBounds.lean#L164-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ProductFactorBounds.lean#L164-L179

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ProductFactorBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.F7 Formalism.FourierDecayAlt.P.ProductFactorBounds

theorem Formalism.FourierDecayAlt.P.all_first_level_weight : Formalism.FourierDecayAlt.F7.AllFirstWeight := by sorry
