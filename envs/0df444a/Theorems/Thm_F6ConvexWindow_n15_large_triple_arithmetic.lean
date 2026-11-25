-- Prove2me | Theorems.Thm_F6ConvexWindow_n15_large_triple_arithmetic
-- name    : F6ConvexWindow.n15_large_triple_arithmetic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:22:25.531313+00:00
-- url     : https://prove2.me/theorems/3c69e627-5fe8-48ca-9bdc-a0cf2b22d902
-- title:
--   F6 Convex Window: n15 large triple arithmetic
-- statement:
--   The three numerical outsider cases in §5; this is only bounded arithmetic.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowN15.lean#L613-L624
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowN15.lean#L613-L624

import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
import Definitions.Def_StableMarriageF6_F6ConvexWindowN15
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.n15_large_triple_arithmetic (t m q e : ℕ) (ht : 6 ≤ t) (htop : 2 * t + 1 ≤ 15)
    (hn : 2 * t + 1 + m + q = 15)
    (he : e ≤ 3 * t + 3 * m + 2 * q + q.choose 2) : e + t ≤ 30 := by sorry
