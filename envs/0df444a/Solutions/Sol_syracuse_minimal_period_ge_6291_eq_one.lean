-- Prove2me | solution 1 for syracuse_minimal_period_ge_6291_eq_one
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @FakeMink
-- created : 2026-10-01T21:59:43.364592+00:00
-- url     : https://prove2.me/submissions/bb248b1d-0e35-4dc5-801d-e5e2628dfb62
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_syracuseStep
import Theorems.Thm_syracuse_cycle_eq_one_of_high_mean_valuation
import Theorems.Thm_syracuse_minimal_period_ge_6291_low_mean_eq_one

set_option autoImplicit false

-- Prospective SKETCH, not a completed proof: the low-mean import is an explicit
-- tracked Open child. Use requires the high-mean theorem actually Proved and
-- fresh exact metadata for that theorem and the published Open child.
theorem solution (m p : ℕ) (hm : 0 < m)
    (hp : 6291 ≤ p) (hcyc : syracuseStep^[p] m = m)
    (hmin : ∀ k : ℕ, 0 < k → k < p → syracuseStep^[k] m ≠ m) :
    m = 1 := by
  by_cases hhigh : 317 * p ≤
      200 * (∑ i ∈ Finset.range p,
        (3 * syracuseStep^[i] m + 1).factorization 2)
  · exact syracuse_cycle_eq_one_of_high_mean_valuation
      m p hm (by omega) hcyc hhigh
  · have hlow : 200 * (∑ i ∈ Finset.range p,
        (3 * syracuseStep^[i] m + 1).factorization 2) < 317 * p := by
      omega
    exact syracuse_minimal_period_ge_6291_low_mean_eq_one
      m p hm hp hcyc hmin hlow
