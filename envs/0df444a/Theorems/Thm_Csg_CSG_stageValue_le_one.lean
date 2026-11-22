-- Prove2me | Theorems.Thm_Csg_CSG_stageValue_le_one
-- name    : Csg.CSG.stageValue_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:42:56.698184+00:00
-- url     : https://prove2.me/theorems/c7c652a6-102c-4459-8f07-976deaa0363b
-- title:
--   CSG: stage Value le one
-- statement:
--   With `C.r ≡ 0`, `stageValue` stays `≤ 1` whenever the continuation does --
--       `MatrixGame.value_le_of_forall_le` applied to `stageGame_A_le_one`. Together with
--       `stageValue_nonneg`, this is exactly the boundedness half the reachability Bellman operator
--       needs to land in `S → Set.Icc (0:ℝ) 1`, not just `S → ℝ`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/CsgMonotone.lean#L127-L130
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/CsgMonotone.lean#L127-L130

import Definitions.Def_Csg_Basic
import Definitions.Def_Csg_CsgMonotone
set_option autoImplicit true
open Csg
open Csg.CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)

theorem Csg.CSG.stageValue_le_one (hr : ∀ s a1 a2, C.r s a1 a2 = 0) {s : S} {v : S → ℝ}
    (hv : ∀ s', v s' ≤ 1) : C.stageValue s v ≤ 1 := by sorry
