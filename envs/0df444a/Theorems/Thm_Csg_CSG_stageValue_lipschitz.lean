-- Prove2me | Theorems.Thm_Csg_CSG_stageValue_lipschitz
-- name    : Csg.CSG.stageValue_lipschitz
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:07:35.351508+00:00
-- url     : https://prove2.me/theorems/a08a8c09-3cab-407a-9bd6-ca7883833829
-- title:
--   CSG: stage Value lipschitz
-- statement:
--   **The payoff.** `stageValue` moves by at most `ε` when the continuation does, in the sup-norm
--       sense (`h`): `MatrixGame.abs_value_sub_le` applied to `stageGame_A_lipschitz`. This is exactly
--       the ingredient Stage 3 needs for `ωScottContinuous`: a monotone chain converging pointwise
--       forces its `stageValue` images to converge to the same limit's `stageValue`, since Lipschitz
--       continuity (in particular, plain continuity) commutes with limits of monotone real sequences
--       the same way it does with any convergent sequence.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/CsgMonotone.lean#L193-L196
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/CsgMonotone.lean#L193-L196

import Definitions.Def_Csg_Basic
import Definitions.Def_Csg_CsgMonotone
set_option autoImplicit true
open Csg
open Csg.CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)

theorem Csg.CSG.stageValue_lipschitz {s : S} {v w : S → ℝ} {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ s', |v s' - w s'| ≤ ε) : |C.stageValue s v - C.stageValue s w| ≤ ε := by sorry
