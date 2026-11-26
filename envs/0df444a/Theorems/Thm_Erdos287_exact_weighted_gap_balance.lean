-- Prove2me | Theorems.Thm_Erdos287_exact_weighted_gap_balance
-- name    : Erdos287.exact_weighted_gap_balance
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T16:42:02.6267+00:00
-- url     : https://prove2.me/theorems/0800f2b2-23a9-482d-ba59-da146f866e78
-- title:
--   Exact weighted identity for gaps of one or two
-- statement:
--   For an increasing finite sequence whose gaps are one or two, twice its selected weight minus the total weight of the full interval equals half the sum of its endpoint weights, plus the average endpoint weights of all unit gaps, plus the average endpoint weight minus midpoint weight of every gap of two. The weight function is arbitrary.
-- source:
--   Erdős #287 effective spacing analysis.

import Mathlib
open Finset

theorem Erdos287.exact_weighted_gap_balance (k : ℕ) (f : ℕ → ℕ) (w : ℕ → ℝ) (hk : 2 ≤ k)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hgap : ∀ i, i + 1 < k → f (i + 1) = f i + 1 ∨ f (i + 1) = f i + 2) :
    let U := (range (k - 1)).filter (fun i => f (i + 1) = f i + 1)
    let V := (range (k - 1)).filter (fun i => f (i + 1) = f i + 2)
    2 * (∑ i ∈ range k, w (f i)) - (∑ n ∈ Icc (f 0) (f (k - 1)), w n) =
      (w (f 0) + w (f (k - 1))) / 2 +
      (∑ i ∈ U, (w (f i) + w (f (i + 1))) / 2) +
      ∑ i ∈ V, ((w (f i) + w (f (i + 1))) / 2 - w (f i + 1)) := by sorry
