-- Prove2me | Theorems.Thm_Bl_general_b_fact_upper_goal1
-- name    : Bl.general_b_fact_upper.goal1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:25:57.924973+00:00
-- url     : https://prove2.me/theorems/a603069b-0475-4cf5-9790-32657e8a95ed
-- title:
--   general b fact upper: goal1
-- statement:
--   The general b fact upper construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactUpper/Imports.lean#L5-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactUpper/Imports.lean#L5-L22

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactUpper_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.general_b_fact_upper

theorem Bl.general_b_fact_upper.goal1 :
  ∀ {K : Type} [inst : NormedField.{0} K] [IsUltrametricDist.{0} K] {x y : K},
  LE.le.{0} (Norm.norm.{0} x) 1 →
    LE.le.{0} (Norm.norm.{0} y) 1 →
      ∀ (n : Nat),
        LE.le.{0} (Norm.norm.{0} (HSub.hSub.{0, 0, 0} (HPow.hPow.{0, 0, 0} x n) (HPow.hPow.{0, 0, 0} y n)))
          (Norm.norm.{0} (HSub.hSub.{0, 0, 0} x y)) := by sorry
