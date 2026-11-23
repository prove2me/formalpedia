-- Prove2me | Theorems.Thm_Bl_general_b_fact_right_side_goal1
-- name    : Bl.general_b_fact_right_side.goal1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:25:59.657664+00:00
-- url     : https://prove2.me/theorems/0f306717-876c-4eb3-a379-98ebbe0a2f22
-- title:
--   general b fact right side: goal1
-- statement:
--   The general b fact right side construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactRightSide/Imports.lean#L5-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactRightSide/Imports.lean#L5-L26

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactRightSide_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.general_b_fact_right_side

theorem Bl.general_b_fact_right_side.goal1 :
  ∀ (x : Real),
  Iff
    (Eq.{1}
      (Complex.exp
        (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} 2 (Complex.ofReal Real.pi)) Complex.I)
          (Complex.ofReal x)))
      1)
    (Exists.{1} fun (n : Int) ↦ Eq.{1} x (Int.cast.{0} n)) := by sorry
