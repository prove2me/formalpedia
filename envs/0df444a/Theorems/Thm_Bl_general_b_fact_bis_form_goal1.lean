-- Prove2me | Theorems.Thm_Bl_general_b_fact_bis_form_goal1
-- name    : Bl.general_b_fact_bis_form.goal1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:50:17.361283+00:00
-- url     : https://prove2.me/theorems/9c0e8e7b-fae3-4b5c-bf04-fba1db9ddc5a
-- title:
--   general b fact bis form: goal1
-- statement:
--   The general b fact bis form construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactBisForm/Imports.lean#L7-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactBisForm/Imports.lean#L7-L57

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactBisForm_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1
open Bl Bl.general_b_fact_bis_form

theorem Bl.general_b_fact_bis_form.goal1 :
  ∀ {F : Type u_1} [inst : NormedAddCommGroup.{u_1} F] [inst_1 : NormedSpace.{0, u_1} Complex F] {U : Set.{u_1} F},
  IsOpen.{u_1} U →
    ∀ {G : F → Complex},
      DifferentiableOn.{0, u_1, 0} Complex G U →
        ∀ {y : F} {R C : Real},
          LT.lt.{0} 0 R →
            LE.le.{u_1} (Metric.closedBall.{u_1} y R) U →
              (∀ (z : F),
                  Membership.mem.{u_1, u_1} (Metric.closedBall.{u_1} y R) z → LE.le.{0} (Norm.norm.{0} (G z)) C) →
                LE.le.{0} (Norm.norm.{u_1} (fderiv.{0, u_1, 0} Complex G y)) (HDiv.hDiv.{0, 0, 0} C R) := by sorry
