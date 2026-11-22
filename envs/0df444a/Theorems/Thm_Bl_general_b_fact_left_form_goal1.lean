-- Prove2me | Theorems.Thm_Bl_general_b_fact_left_form_goal1
-- name    : Bl.general_b_fact_left_form.goal1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:20:06.915144+00:00
-- url     : https://prove2.me/theorems/f60f514c-f743-40af-a56c-99fbf79e2526
-- title:
--   general b fact left form: goal1
-- statement:
--   The general b fact left form construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactLeftForm/Imports.lean#L8-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactLeftForm/Imports.lean#L8-L32

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactLeftForm_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
universe u v w
open Bl Bl.general_b_fact_left_form

theorem Bl.general_b_fact_left_form.goal1 {n : ℕ} (f : Fin n → ℝ) (hf : Antitone f) (θ : ℝ) (j : Fin n) :
    θ ≤ f j ↔ (j : ℕ) < (Finset.univ.filter (fun i => θ ≤ f i)).card := by sorry
