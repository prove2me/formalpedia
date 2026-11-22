-- Prove2me | Theorems.Thm_Csg_CSG_expect_mono
-- name    : Csg.CSG.expect_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:06:15.943705+00:00
-- url     : https://prove2.me/theorems/f0f1d454-4449-4dc1-8f21-81409203a65d
-- title:
--   CSG: expect mono
-- statement:
--   `expect` is monotone in the continuation `v`: it's a weighted average with nonnegative
--       weights (transition probabilities), so raising `v` pointwise can only raise the average.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/CsgMonotone.lean#L52-L55
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/CsgMonotone.lean#L52-L55

import Definitions.Def_Csg_Basic
import Definitions.Def_Csg_CsgMonotone
set_option autoImplicit true
open Csg
open Csg.CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)

theorem Csg.CSG.expect_mono {s : S} {a1 : A1} {a2 : A2} {v w : S → ℝ} (hle : ∀ s', v s' ≤ w s') :
    C.expect s a1 a2 v ≤ C.expect s a1 a2 w := by sorry
