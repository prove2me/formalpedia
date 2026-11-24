-- Prove2me | Theorems.Thm_Bl_general_b_fact_left_ter_form_goal1
-- name    : Bl.general_b_fact_left_ter_form.goal1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:20.619798+00:00
-- url     : https://prove2.me/theorems/57e30c8c-f334-4144-8b12-e62a0cca00a9
-- title:
--   general b fact left ter form: goal1
-- statement:
--   The general b fact left ter form construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactLeftTerForm/Imports.lean#L5-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactLeftTerForm/Imports.lean#L5-L35

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactLeftTerForm_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.general_b_fact_left_ter_form

theorem Bl.general_b_fact_left_ter_form.goal1 :
  ∀ {R K V : Type} [inst : CommRing.{0} R] [IsDomain.{0} R] [inst_2 : Field.{0} K] [inst_3 : Algebra.{0, 0} R K]
  [IsFractionRing.{0, 0} R K] [inst_5 : AddCommGroup.{0} V] [inst_6 : Module.{0, 0} R V] [inst_7 : Module.{0, 0} K V]
  [IsScalarTower.{0, 0, 0} R K V] (M : Submodule.{0, 0} R V) (y : V),
  Membership.mem.{0, 0} (Submodule.span.{0, 0} K (SetLike.coe.{0, 0} M)) y →
    Exists.{1} fun (s : R) ↦ And (Ne.{1} s 0) (Membership.mem.{0, 0} M (HSMul.hSMul.{0, 0, 0} s y)) := by sorry
