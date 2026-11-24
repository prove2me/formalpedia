-- Prove2me | Theorems.Thm_Bl_general_b_fact_ter_form_goal1
-- name    : Bl.general_b_fact_ter_form.goal1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:19.792685+00:00
-- url     : https://prove2.me/theorems/eadf54cc-3046-4ba0-a44f-8c10618da143
-- title:
--   general b fact ter form: goal1
-- statement:
--   The general b fact ter form construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactTerForm/Imports.lean#L5-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactTerForm/Imports.lean#L5-L29

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactTerForm_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.general_b_fact_ter_form

theorem Bl.general_b_fact_ter_form.goal1 :
  ∀ {x : WithBot.{0} ENat} {m : Nat},
  Eq.{1} (HAdd.hAdd.{0, 0, 0} x 1) (Nat.cast.{0} (HAdd.hAdd.{0, 0, 0} m 1)) → Eq.{1} x (Nat.cast.{0} m) := by sorry
