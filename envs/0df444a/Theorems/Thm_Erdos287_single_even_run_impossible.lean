-- Prove2me | Theorems.Thm_Erdos287_single_even_run_impossible
-- name    : Erdos287.single_even_run_impossible
-- status  : Open
-- author  : @junyihjy
-- created : 2026-09-30T16:34:45.699867+00:00
-- url     : https://prove2.me/theorems/ecba8028-304b-4109-920b-4e57ae3d421f
-- title:
--   One even block plus odd reciprocals cannot sum to 1
-- statement:
--   Let 2m, 2(m+1), ..., 2(m+t-1) be a nonempty block of consecutive even integers with reciprocal sum B, and let O be any sum of reciprocals of odd positive integers. Then B + O != 1. Proof idea: the halved block m, ..., m+t-1 has a unique element of maximal 2-adic valuation c (Kurschak), so the 2-adic norm of B is 2^(c+1) > 1 while the norm of O is at most 1; the ultrametric inequality gives |B + O|_2 = |B|_2 > 1 = |1|_2. This is the one-even-run case of Erdos287.mixed_gap_core -- the single-block analogue of the proved Erdos287.even_blocks_distinct_norm. Together they force any hypothetical gap-<=2 representation to have at least two even runs, all of equal 2-adic weight.
-- source:
--   Decomposition of the residual core Erdos287.mixed_gap_core (Erdos problem #287).

import Mathlib

namespace Erdos287
theorem single_even_run_impossible (m t : ℕ) (hm : 0 < m) (ht : 0 < t)
    (s : Finset ℕ) (g : ℕ → ℕ) (hodd : ∀ x ∈ s, ¬ 2 ∣ g x) (hg : ∀ x ∈ s, g x ≠ 0) :
    Finset.sum (Finset.range t) (fun j => (1 : ℚ) / ((2 * (m + j) : ℕ) : ℚ))
      + Finset.sum s (fun x => (1 : ℚ) / (g x : ℚ)) ≠ 1 := by sorry
end Erdos287
