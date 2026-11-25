-- Prove2me | Theorems.Thm_Bl_general_b_fact_third_last_goal1
-- name    : Bl.general_b_fact_third_last.goal1
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:16:00.773406+00:00
-- url     : https://prove2.me/theorems/34954a95-bbf3-546f-aece-27d77045a6d3
-- title:
--   general b fact third last: goal1
-- statement:
--   The general b fact third last construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactThirdLast/Imports.lean#L5-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactThirdLast/Imports.lean#L5-L21

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactThirdLast_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.general_b_fact_third_last

theorem Bl.general_b_fact_third_last.goal1 :
  ∀ {a : WithBot.{0} ENat} {n : Nat},
  Eq.{1} (HAdd.hAdd.{0, 0, 0} a 1) (Nat.cast.{0} (HAdd.hAdd.{0, 0, 0} n 1)) → Eq.{1} a (Nat.cast.{0} n) := by sorry
