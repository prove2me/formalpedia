-- Prove2me | solution 1 for syracuse_cycle_min_bound
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-08T20:20:15.583971+00:00
-- url     : https://prove2.me/submissions/2a6cbb34-64dd-4258-9070-8a4c61ba52ab

import Mathlib
import Definitions.Def_syracuseStep
import Theorems.Thm_syracuse_cycle_pow_two_gt_pow_three
import Theorems.Thm_syracuse_cycle_min_upper_bound

theorem solution (m a : ℕ) (hm : 0 < m) (ha : 0 < a)
    (hcyc : syracuseStep^[a] m = m)
    (hmin : ∀ i : ℕ, m ≤ syracuseStep^[i] m) :
    (3 ^ a + 1) * m ^ a ≤ (3 * m + 1) ^ a := by
  have hlow : 3 ^ a + 1
      ≤ 2 ^ (∑ i ∈ Finset.range a, (3 * syracuseStep^[i] m + 1).factorization 2) :=
    syracuse_cycle_pow_two_gt_pow_three m a hm ha hcyc
  calc (3 ^ a + 1) * m ^ a
      ≤ 2 ^ (∑ i ∈ Finset.range a, (3 * syracuseStep^[i] m + 1).factorization 2) * m ^ a :=
        Nat.mul_le_mul_right _ hlow
    _ ≤ (3 * m + 1) ^ a := syracuse_cycle_min_upper_bound m a hm ha hcyc hmin
