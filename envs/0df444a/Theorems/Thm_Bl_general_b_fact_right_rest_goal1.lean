-- Prove2me | Theorems.Thm_Bl_general_b_fact_right_rest_goal1
-- name    : Bl.general_b_fact_right_rest.goal1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:19:58.188096+00:00
-- url     : https://prove2.me/theorems/a2120215-80e6-479d-858d-b790abedd77d
-- title:
--   general b fact right rest: goal1
-- statement:
--   The general b fact right rest construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactRightRest/Imports.lean#L25-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactRightRest/Imports.lean#L25-L30

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactRightRest_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open Bl Bl.general_b_fact_right_rest

theorem Bl.general_b_fact_right_rest.goal1 :
  ∀ {α : Type u_1} {β : Type u_2} [DecidableEq.{u_2 + 1} β] (f : α → β) (t : Multiset.{u_1} α) (s : Multiset.{u_2} β),
  LE.le.{u_2} s (Multiset.map.{u_2, u_1} f t) →
    Exists.{u_1 + 1} fun (u : Multiset.{u_1} α) ↦ And (LE.le.{u_1} u t) (Eq.{u_2 + 1} (Multiset.map.{u_2, u_1} f u) s) := by sorry
