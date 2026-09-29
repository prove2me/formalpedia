-- Prove2me | Theorems.Thm_BlockCycleRotation_outer_layer
-- name    : BlockCycleRotation.outer_layer
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:56:55.804575+00:00
-- url     : https://prove2.me/theorems/a12ae1fb-f980-4ace-891d-9d1f580a08f7
-- title:
--   The outer estimation layer: summing over divisors
-- statement:
--   For $n>0$,
--   $$\sum_{d \mid n} \left(\sqrt{\tfrac{n/d-1}{d}}+1\right) 3\,\frac{n}{d}\left(1+\log\frac{n}{d}\right) \le \tau(n) \left(\sqrt{n}+1\right) 3n\,(1+\log n),$$
--   where $\tau(n)$ is the number of divisors. Each summand is bounded by its value at $d=1$ and the sum has $\tau(n)$ terms.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Lemmas 16 and 18. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/TripleSum.lean#L1068-L1105

import Mathlib

open Real Finset

theorem BlockCycleRotation.outer_layer {n : ℕ} (hn : 0 < n) :
    ∑ d ∈ n.divisors,
        ((Nat.sqrt ((n / d - 1) / d) : ℝ) + 1)
          * (3 * ((n / d : ℕ) : ℝ) * (1 + Real.log ((n / d : ℕ) : ℝ)))
      ≤ (n.divisors.card : ℝ)
          * (((Nat.sqrt n : ℝ) + 1) * (3 * (n : ℝ) * (1 + Real.log n))) := by sorry
