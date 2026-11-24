-- Prove2me | Theorems.Thm_Bl_general_b_fact_bis_goal1
-- name    : Bl.general_b_fact_bis.goal1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:33:32.395411+00:00
-- url     : https://prove2.me/theorems/6e8b1347-fa87-4c2a-8e64-65d975cfc95b
-- title:
--   general b fact bis: goal1
-- statement:
--   The general b fact bis construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactBis/Imports.lean#L5-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactBis/Imports.lean#L5-L23

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactBis_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.general_b_fact_bis

theorem Bl.general_b_fact_bis.goal1 :
  ∀ {x : WithBot.{0} ENat} {m : Nat},
  Eq.{1} (HAdd.hAdd.{0, 0, 0} x 1) (Nat.cast.{0} (HAdd.hAdd.{0, 0, 0} m 1)) → Eq.{1} x (Nat.cast.{0} m) := by sorry
