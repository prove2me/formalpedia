-- Prove2me | Theorems.Thm_Csg_CSG_stageGame_A_nonneg
-- name    : Csg.CSG.stageGame_A_nonneg
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:06:46.752582+00:00
-- url     : https://prove2.me/theorems/2c6c4a25-4a44-44f9-8d89-12a11f2ddc4e
-- title:
--   CSG: stage Game A nonneg
-- statement:
--   With `C.r ≡ 0`, the stage game's payoff matrix stays nonnegative whenever the continuation
--       does -- immediate from `expect_nonneg` once the (zero) reward term is dropped.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/CsgMonotone.lean#L94-L98
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/CsgMonotone.lean#L94-L98

import Definitions.Def_Csg_Basic
import Definitions.Def_Csg_CsgMonotone
set_option autoImplicit true
open Csg
open Csg.CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)

theorem Csg.CSG.stageGame_A_nonneg (hr : ∀ s a1 a2, C.r s a1 a2 = 0) {s : S} {v : S → ℝ}
    (hv : ∀ s', 0 ≤ v s') (a1 : A1) (a2 : A2) : 0 ≤ (C.stageGame s v).A a1 a2 := by sorry
