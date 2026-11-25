-- Prove2me | Theorems.Thm_Bl_general_b_fact_left_goal1
-- name    : Bl.general_b_fact_left.goal1
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:52:06.841577+00:00
-- url     : https://prove2.me/theorems/f10d012a-44f8-5b8e-a1f9-a56025941f7a
-- title:
--   general b fact left: goal1
-- statement:
--   The general b fact left construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactLeft/Imports.lean#L5-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactLeft/Imports.lean#L5-L58

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactLeft_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.general_b_fact_left

theorem Bl.general_b_fact_left.goal1 :
  ∀ {k : Type} [inst : Field.{0} k] [Fintype.{0} k] (t m e : k),
  Ne.{1} (HSub.hSub.{0, 0, 0} (HPow.hPow.{0, 0, 0} t 2) (HMul.hMul.{0, 0, 0} 4 m)) 0 →
    Exists.{1} fun (x : k) ↦
      Exists.{1} fun (y : k) ↦
        Eq.{1}
          (HAdd.hAdd.{0, 0, 0}
            (HAdd.hAdd.{0, 0, 0} (HPow.hPow.{0, 0, 0} x 2) (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} t x) y))
            (HMul.hMul.{0, 0, 0} m (HPow.hPow.{0, 0, 0} y 2)))
          e := by sorry
