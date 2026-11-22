-- Prove2me | Theorems.Thm_Csg_CSG_stageGame_A_le_one
-- name    : Csg.CSG.stageGame_A_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:06:48.678785+00:00
-- url     : https://prove2.me/theorems/7766ca78-dfce-46c4-b4ac-d2f2df6f1987
-- title:
--   CSG: stage Game A le one
-- statement:
--   With `C.r ≡ 0`, the stage game's payoff matrix stays `≤ 1` whenever the continuation does --
--       immediate from `expect_le_one` once the (zero) reward term is dropped.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/CsgMonotone.lean#L102-L106
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/CsgMonotone.lean#L102-L106

import Definitions.Def_Csg_Basic
import Definitions.Def_Csg_CsgMonotone
set_option autoImplicit true
open Csg
open Csg.CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)

theorem Csg.CSG.stageGame_A_le_one (hr : ∀ s a1 a2, C.r s a1 a2 = 0) {s : S} {v : S → ℝ}
    (hv : ∀ s', v s' ≤ 1) (a1 : A1) (a2 : A2) : (C.stageGame s v).A a1 a2 ≤ 1 := by sorry
