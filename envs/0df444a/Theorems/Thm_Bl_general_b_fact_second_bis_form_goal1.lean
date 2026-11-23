-- Prove2me | Theorems.Thm_Bl_general_b_fact_second_bis_form_goal1
-- name    : Bl.general_b_fact_second_bis_form.goal1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:25:48.388329+00:00
-- url     : https://prove2.me/theorems/d7610983-edfb-4ebb-a4cc-d37d1fde03a4
-- title:
--   general b fact second bis form: goal1
-- statement:
--   The general b fact second bis form construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactSecondBisForm/Goal1.lean#L7-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactSecondBisForm/Goal1.lean#L7-L63

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open Bl Bl.general_b_fact_second_bis_form

theorem Bl.general_b_fact_second_bis_form.goal1 :
  ∀ {E : Type u_1} {F : Type u_2} [inst : NormedAddCommGroup.{u_1} E] [inst_1 : NormedSpace.{0, u_1} Complex E]
  [inst_2 : NormedAddCommGroup.{u_2} F] [inst_3 : NormedSpace.{0, u_2} Complex F] {f : E → F} {y : E} {δ M : Real},
  LT.lt.{0} 0 δ →
    DifferentiableOn.{0, u_1, u_2} Complex f (Metric.ball.{u_1} y δ) →
      (∀ (z : E), Membership.mem.{u_1, u_1} (Metric.ball.{u_1} y δ) z → LE.le.{0} (Norm.norm.{u_2} (f z)) M) →
        LE.le.{0} (Norm.norm.{max u_2 u_1} (fderiv.{0, u_1, u_2} Complex f y)) (HDiv.hDiv.{0, 0, 0} M δ) := by sorry
