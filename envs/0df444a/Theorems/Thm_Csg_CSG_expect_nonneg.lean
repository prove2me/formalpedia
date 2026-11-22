-- Prove2me | Theorems.Thm_Csg_CSG_expect_nonneg
-- name    : Csg.CSG.expect_nonneg
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:06:32.957498+00:00
-- url     : https://prove2.me/theorems/f31cbc14-8f75-40ad-ba38-5235b50fae0c
-- title:
--   CSG: expect nonneg
-- statement:
--   `expect` stays nonnegative whenever the continuation does -- same nonnegative-weights fact,
--       the degenerate case of monotonicity against the constant continuation `0`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/CsgMonotone.lean#L59-L62
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/CsgMonotone.lean#L59-L62

import Definitions.Def_Csg_Basic
import Definitions.Def_Csg_CsgMonotone
set_option autoImplicit true
open Csg
open Csg.CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)

theorem Csg.CSG.expect_nonneg {s : S} {a1 : A1} {a2 : A2} {v : S → ℝ} (hv : ∀ s', 0 ≤ v s') :
    0 ≤ C.expect s a1 a2 v := by sorry
