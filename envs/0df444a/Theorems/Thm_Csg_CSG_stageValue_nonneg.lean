-- Prove2me | Theorems.Thm_Csg_CSG_stageValue_nonneg
-- name    : Csg.CSG.stageValue_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:43:53.259055+00:00
-- url     : https://prove2.me/theorems/43934d40-bb5e-4b66-bf35-36b667f830d7
-- title:
--   CSG: stage Value nonneg
-- statement:
--   With `C.r ≡ 0`, `stageValue` stays nonnegative whenever the continuation does --
--       `MatrixGame.le_value_of_forall_le` applied to `stageGame_A_nonneg`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/CsgMonotone.lean#L118-L121
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/CsgMonotone.lean#L118-L121

import Definitions.Def_Csg_Basic
import Definitions.Def_Csg_CsgMonotone
set_option autoImplicit true
open Csg
open Csg.CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)

theorem Csg.CSG.stageValue_nonneg (hr : ∀ s a1 a2, C.r s a1 a2 = 0) {s : S} {v : S → ℝ}
    (hv : ∀ s', 0 ≤ v s') : 0 ≤ C.stageValue s v := by sorry
