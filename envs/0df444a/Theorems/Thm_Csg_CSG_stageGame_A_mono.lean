-- Prove2me | Theorems.Thm_Csg_CSG_stageGame_A_mono
-- name    : Csg.CSG.stageGame_A_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:06:34.846486+00:00
-- url     : https://prove2.me/theorems/9d203d5f-e907-4b8c-b0cf-4e8d8661123d
-- title:
--   CSG: stage Game A mono
-- statement:
--   The stage game's payoff matrix is monotone in the continuation `v`, entrywise -- the reward
--       term doesn't move, and `expect` is monotone (`expect_mono`).
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/CsgMonotone.lean#L86-L90
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/CsgMonotone.lean#L86-L90

import Definitions.Def_Csg_Basic
import Definitions.Def_Csg_CsgMonotone
set_option autoImplicit true
open Csg
open Csg.CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)

theorem Csg.CSG.stageGame_A_mono {s : S} {v w : S → ℝ} (hle : ∀ s', v s' ≤ w s') (a1 : A1) (a2 : A2) :
    (C.stageGame s v).A a1 a2 ≤ (C.stageGame s w).A a1 a2 := by sorry
