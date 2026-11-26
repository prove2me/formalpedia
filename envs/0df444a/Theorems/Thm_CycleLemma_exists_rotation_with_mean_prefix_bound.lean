-- Prove2me | Theorems.Thm_CycleLemma_exists_rotation_with_mean_prefix_bound
-- name    : CycleLemma.exists_rotation_with_mean_prefix_bound
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T06:46:34.377913+00:00
-- url     : https://prove2.me/theorems/196c2e2a-2520-595b-b390-0e8584c807cc
-- title:
--   A cyclic rotation whose prefix means are bounded by the overall mean
-- statement:
--   Every finite list of $n$ natural numbers has a cyclic rotation for which each prefix of length $j$ and sum $p$ satisfies $np\le jS$, where $S$ is the sum of the list. This includes empty lists and empty prefixes.
--
--   The same cut works simultaneously for all prefix lengths.
-- source:
--   Local derivation: SyracuseShortHorizon.lean, exists_rotation_with_mean_prefix_bound, using the maximal partial-sum argument for cyclic sequences. Original declaration starts at line 79. Apply the zero-sum cyclic partial-sum observation in K. Ford, Integers with a divisor in (y, 2y], Section 2 immediately before Lemma 2.4, https://www.ford126.web.illinois.edu/wwwpapers/hxy2y.pdf, to the centered sequence with sign reversed.

import Mathlib

theorem CycleLemma.exists_rotation_with_mean_prefix_bound (w : List ℕ) :
    ∃ r ≤ w.length, ∀ j ≤ w.length,
      w.length * ((w.rotate r).take j).sum ≤ j * w.sum := by sorry
