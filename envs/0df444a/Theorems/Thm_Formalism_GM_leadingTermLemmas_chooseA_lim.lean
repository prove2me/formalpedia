-- Prove2me | Theorems.Thm_Formalism_GM_leadingTermLemmas_chooseA_lim
-- name    : Formalism.GM.leadingTermLemmas.chooseA_lim
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:24:45.043854+00:00
-- url     : https://prove2.me/theorems/01af92f1-288c-40d4-8f5c-8c8279d59625
-- title:
--   leading Term Lemmas: choose A lim
-- statement:
--   The leading Term Lemmas construction uses the choose A lim property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L1459-L1463
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L1459-L1463

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
open MvPolynomial Finset Formalism.GM Filter Topology

theorem Formalism.GM.leadingTermLemmas.chooseA_lim (o z r : ℕ) :
    Tendsto (fun n : ℕ => ((o + n + r + z - 1).choose o : ℝ) / (n : ℝ) ^ o) atTop (𝓝 (1 / (o.factorial : ℝ))) := by sorry
