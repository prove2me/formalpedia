-- Prove2me | Theorems.Thm_Formalism_GM_windowFullAP_of
-- name    : Formalism.GM.windowFullAP_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:51:43.731564+00:00
-- url     : https://prove2.me/theorems/7d0e94b7-4ced-4059-8a5f-26893282c4e6
-- title:
--   GM: window Full AP of
-- statement:
--   The GM construction uses the window Full AP of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WindowMeanAP.lean#L116-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WindowMeanAP.lean#L116-L128

import Definitions.Def_Formalism_MahlerMeasure_QuotientUpperBoundsOfPowerBounds
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_DeterminantBlockLeadingTerm
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WindowMeanAP
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM
open Finset Polynomial ProgressionMeanBounds

theorem Formalism.GM.windowFullAP_of (hL : ValuationWindowLowerBound) (hW : WindowMeanAP) : WindowFullAP := by sorry
