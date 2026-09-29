-- Prove2me | Theorems.Thm_Erdos146_hammingRetentionMeasure_integrable
-- name    : Erdos146.hammingRetentionMeasure_integrable
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T04:47:37.526276+00:00
-- url     : https://prove2.me/theorems/5d0a4653-55c9-444e-9764-38f793df8353
-- title:
--   Retained counts are integrable
-- statement:
--   Supporting fact for the sampled Hamming-ball graph of Section 7. The host is the sampled Hamming-ball graph of Section 7: with $U = \{0,1\}^m$, two disjoint copies $U_L, U_R$ are joined whenever their Hamming distance is at most $k = \lfloor \tau m \rfloor$, and each vertex is retained independently with probability $p = 2^{-\beta m}$. The retained-vertex and retained-edge counts are integrable for the retention measure, so their expectations are defined.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L14806-L14814

import Definitions.Def_erdos146_core2
import Mathlib.MeasureTheory.Function.L1Space.Integrable

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem Erdos146.hammingRetentionMeasure_integrable
    (dimension : ℕ)
    (observable : Set (Bool × HammingWord dimension) → ℝ) :
    MeasureTheory.Integrable observable
      (hammingRetentionMeasure dimension) := by sorry
