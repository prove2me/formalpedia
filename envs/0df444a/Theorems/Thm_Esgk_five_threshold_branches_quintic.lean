-- Prove2me | Theorems.Thm_Esgk_five_threshold_branches_quintic
-- name    : Esgk.five_threshold_branches_quintic
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-14T02:15:06.169711+00:00
-- url     : https://prove2.me/theorems/37f5248b-09cb-428f-998f-36658724feca
-- title:
--   Compress five threshold branches to one quintic bound
-- statement:
--   Let $n,s,T,C$ be natural numbers with $s>0$ and $T>0$. Suppose at least one of the five bounds
--
--   $$
--   n\le3s,\quad n\le s^2,\quad n\le s,\quad n^2<128T s^7,\quad n\le32C s^5
--   $$
--
--   holds. Then, with
--
--   $$
--   A=\max\{3,128T,32C\},
--   $$
--
--   one has $n\le A s^5$. This is a reusable exact-arithmetic compressor for the five branches of the deficiency bootstrap.
-- source:
--   Exact arithmetic in Section N15-F6 of https://github.com/flound1129/esgk-on3/blob/8a4c11ac6083f1c5e354b1a2556eae086f4b3ee5/docs/plans/esgk-n15-formalization-plan-2026-08-25.md

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import Mathlib

namespace Esgk

/-- Each of the five threshold branches is bounded by one uniform quintic expression. -/
theorem five_threshold_branches_quintic
    (n s T C : ℕ) (hs : 0 < s) (hT : 0 < T)
    (hbranches : n ≤ 3 * s ∨ n ≤ s ^ 2 ∨ n ≤ s ∨
      n ^ 2 < 128 * T * s ^ 7 ∨ n ≤ 32 * C * s ^ 5) :
    n ≤ max 3 (max (128 * T) (32 * C)) * s ^ 5 := by
  sorry

end Esgk
