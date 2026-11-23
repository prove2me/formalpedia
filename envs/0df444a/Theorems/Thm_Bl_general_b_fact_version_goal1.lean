-- Prove2me | Theorems.Thm_Bl_general_b_fact_version_goal1
-- name    : Bl.general_b_fact_version.goal1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:17:35.898796+00:00
-- url     : https://prove2.me/theorems/546e32d5-12e1-4390-bf0c-f522d622cf55
-- title:
--   general b fact version: goal1
-- statement:
--   The general b fact version construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactVersion/Imports.lean#L7-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactVersion/Imports.lean#L7-L26

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactVersion_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1
open Bl Bl.general_b_fact_version

theorem Bl.general_b_fact_version.goal1 :
  ∀ {Y : Type u_1} [inst : NormedAddCommGroup.{u_1} Y] [inst_1 : NormedSpace.{0, u_1} Complex Y] {g : Y → Complex} {y : Y}
  {R M : Real},
  LT.lt.{0} 0 R →
    DifferentiableOn.{0, u_1, 0} Complex g (Metric.ball.{u_1} y (HMul.hMul.{0, 0, 0} 2 R)) →
      (∀ (v : Y),
          Membership.mem.{u_1, u_1} (Metric.ball.{u_1} y (HMul.hMul.{0, 0, 0} 2 R)) v →
            LE.le.{0} (Norm.norm.{0} (g v)) M) →
        LE.le.{0} (Norm.norm.{u_1} (fderiv.{0, u_1, 0} Complex g y)) (HDiv.hDiv.{0, 0, 0} M R) := by sorry
