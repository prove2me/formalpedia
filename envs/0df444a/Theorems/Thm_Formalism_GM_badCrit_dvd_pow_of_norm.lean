-- Prove2me | Theorems.Thm_Formalism_GM_badCrit_dvd_pow_of_norm
-- name    : Formalism.GM.badCrit_dvd_pow_of_norm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:22:52.815071+00:00
-- url     : https://prove2.me/theorems/ff6f349a-834f-4dba-8a8d-19a655a341e5
-- title:
--   GM: bad Crit dvd pow of norm
-- statement:
--   The GM construction uses the bad Crit dvd pow of norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/BadCrit.lean#L7-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/BadCrit.lean#L7-L26

import Definitions.Def_Formalism_MahlerMeasure_StatementT
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_BadCrit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM
open Module

theorem Formalism.GM.badCrit_dvd_pow_of_norm {p : ℕ} [Fact p.Prime] {a : ℤ_[p]} {E : ℕ}
    (h : (p : ℝ) ^ (-(E : ℤ)) ≤ ‖a‖) : a ∣ (p : ℤ_[p]) ^ E := by sorry
