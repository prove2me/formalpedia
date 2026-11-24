-- Prove2me | Theorems.Thm_Formalism_GM_leadingTermLemmas_choose_lim
-- name    : Formalism.GM.leadingTermLemmas.choose_lim
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:25:30.713591+00:00
-- url     : https://prove2.me/theorems/efb4b256-1885-4ac5-9bf4-d09e0a141186
-- title:
--   leading Term Lemmas: choose lim
-- statement:
--   The leading Term Lemmas construction uses the choose lim property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L1196-L1217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L1196-L1217

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamLead
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.leadingTermLemmas
open Filter Topology Finset

theorem Formalism.GM.leadingTermLemmas.choose_lim (c s j : ℕ) :
    Tendsto (fun n : ℕ => ((n + c - s).choose j : ℝ) / (n : ℝ) ^ j) atTop (𝓝 (1 / (j.factorial : ℝ))) := by sorry
