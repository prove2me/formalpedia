-- Prove2me | Theorems.Thm_Csg_CSG_stageValue_mono
-- name    : Csg.CSG.stageValue_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:42:55.203823+00:00
-- url     : https://prove2.me/theorems/d5387db4-2b21-46bc-93bc-211e0358f99a
-- title:
--   CSG: stage Value mono
-- statement:
--   **The payoff.** `stageValue` is monotone in the continuation `v`: `MatrixGame.value_mono`
--       applied to `stageGame_A_mono`. This is exactly what makes the reachability Bellman operator
--       (next artifact) an `OrderHom`, not just a function.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/CsgMonotone.lean#L111-L114
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/CsgMonotone.lean#L111-L114

import Definitions.Def_Csg_Basic
import Definitions.Def_Csg_CsgMonotone
set_option autoImplicit true
open Csg
open Csg.CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)

theorem Csg.CSG.stageValue_mono {s : S} {v w : S → ℝ} (hle : ∀ s', v s' ≤ w s') :
    C.stageValue s v ≤ C.stageValue s w := by sorry
