-- Prove2me | Theorems.Thm_Csg_CSG_stageGame_A_lipschitz
-- name    : Csg.CSG.stageGame_A_lipschitz
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:06:55.722331+00:00
-- url     : https://prove2.me/theorems/08f9549c-c30e-4d47-817a-b4a56f88fb2d
-- title:
--   CSG: stage Game A lipschitz
-- statement:
--   The stage game's payoff matrix moves by at most `ε` when the continuation does, entrywise --
--       the reward term doesn't depend on `v` at all, so it cancels exactly out of the difference,
--       leaving `expect_lipschitz`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/CsgMonotone.lean#L177-L185
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/CsgMonotone.lean#L177-L185

import Definitions.Def_Csg_Basic
import Definitions.Def_Csg_CsgMonotone
set_option autoImplicit true
open Csg
open Csg.CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)

theorem Csg.CSG.stageGame_A_lipschitz {s : S} {v w : S → ℝ} {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ s', |v s' - w s'| ≤ ε) (a1 : A1) (a2 : A2) :
    |(C.stageGame s v).A a1 a2 - (C.stageGame s w).A a1 a2| ≤ ε := by sorry
