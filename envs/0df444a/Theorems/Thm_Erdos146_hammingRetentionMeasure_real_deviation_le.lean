-- Prove2me | Theorems.Thm_Erdos146_hammingRetentionMeasure_real_deviation_le
-- name    : Erdos146.hammingRetentionMeasure_real_deviation_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T04:48:27.909544+00:00
-- url     : https://prove2.me/theorems/b57cefff-b487-4897-a305-4f7bd02da68c
-- title:
--   Deviation bound for the retention measure
-- statement:
--   Supporting fact for the sampled Hamming-ball graph of Section 7. The host is the sampled Hamming-ball graph of Section 7: with $U = \{0,1\}^m$, two disjoint copies $U_L, U_R$ are joined whenever their Hamming distance is at most $k = \lfloor \tau m \rfloor$, and each vertex is retained independently with probability $p = 2^{-\beta m}$. Chebyshev-type deviation bound for the retained counts, the quantitative core of the second-moment argument.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L14885-L14915

import Definitions.Def_erdos146_core2
import Mathlib.Data.Real.StarOrdered
import Mathlib.Probability.Moments.Variance

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem Erdos146.hammingRetentionMeasure_real_deviation_le
    (dimension : ℕ)
    (observable : Set (Bool × HammingWord dimension) → ℝ)
    (threshold : ℝ) (hthreshold : 0 < threshold) :
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        threshold ≤
          |observable retained -
            (∫ candidate,
              observable candidate ∂hammingRetentionMeasure dimension)|} ≤
      ProbabilityTheory.variance observable
          (hammingRetentionMeasure dimension) /
        threshold ^ 2 := by sorry
