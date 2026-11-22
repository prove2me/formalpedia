-- Prove2me | Theorems.Thm_Csg_CSG_expect_le_one
-- name    : Csg.CSG.expect_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:06:36.348952+00:00
-- url     : https://prove2.me/theorems/687735a3-a7c3-4f68-9668-40c6a3cbf24c
-- title:
--   CSG: expect le one
-- statement:
--   `expect` stays `≤ 1` whenever the continuation does: bound each term by the weight itself
--       (since `v s' ≤ 1`), then the weights themselves sum to at most `1` -- a transition kernel is
--       a genuine `PMF`, `Finset.univ`'s mass can't exceed the total mass `PMF.tsum_coe` fixes at
--       `1`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/CsgMonotone.lean#L68-L82
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/CsgMonotone.lean#L68-L82

import Definitions.Def_Csg_Basic
import Definitions.Def_Csg_CsgMonotone
set_option autoImplicit true
open Csg
open Csg.CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)

theorem Csg.CSG.expect_le_one {s : S} {a1 : A1} {a2 : A2} {v : S → ℝ} (hv : ∀ s', v s' ≤ 1) :
    C.expect s a1 a2 v ≤ 1 := by sorry
