-- Prove2me | Theorems.Thm_Erdos146_hammingRetentionMeasure_integral_eq_sum
-- name    : Erdos146.hammingRetentionMeasure_integral_eq_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T04:48:02.373611+00:00
-- url     : https://prove2.me/theorems/d96f2626-48ae-418c-addc-2abf9d5a0970
-- title:
--   Expectation as a sum over words
-- statement:
--   Supporting fact for the sampled Hamming-ball graph of Section 7. The host is the sampled Hamming-ball graph of Section 7: with $U = \{0,1\}^m$, two disjoint copies $U_L, U_R$ are joined whenever their Hamming distance is at most $k = \lfloor \tau m \rfloor$, and each vertex is retained independently with probability $p = 2^{-\beta m}$. The integral of a function against the retention measure is the corresponding sum over Boolean words weighted by retention probability.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L14826-L14837

import Definitions.Def_erdos146_core2
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem Erdos146.hammingRetentionMeasure_integral_eq_sum
    (dimension : ℕ)
    (observable : Set (Bool × HammingWord dimension) → ℝ) :
    (∫ retained,
      observable retained ∂hammingRetentionMeasure dimension) =
      ∑ retained : Set (Bool × HammingWord dimension),
        (hammingRetentionMeasure dimension).real {retained} *
          observable retained := by sorry
