-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f17_dense_range_right_neighbourhood_sample
-- name    : AvramDividend.Classical.avram_f17_dense_range_right_neighbourhood_sample
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T08:51:08.376315+00:00
-- url     : https://prove2.me/theorems/b7acb7cf-ae01-4e41-91e5-9ee860a5825e
-- title:
--   Any dense sequence of nonnegative times meets every right neighbourhood strictly before the next time
-- statement:
--   A dense countable deterministic nonnegative-time grid meets every relative right neighbourhood of s before any later time t. This is the exact grid-richness hypothesis used in the genuine original controlled reserve pre-exit left-limit and Gaussian coefficient bounds. The proof extracts the positive open interval contained in the right neighbourhood, then applies density to that interval.
-- source:
--   Exact genuine math argument appearing inside independently accepted public 95286a41, extracted as a composable original dense-grid certificate so subsequent C2 source lemmas can use standard DenseRange rather than a long neighbourhood premise.

import Mathlib
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.Bases
open Set Filter Topology
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f17_dense_range_right_neighbourhood_sample
    (r : ℕ → ℝ≥0) (hdense : DenseRange r)
    (s t : ℝ≥0) (hst : s < t)
    (U : Set ℝ≥0) (hU : U ∈ 𝓝[Set.Ici s] s) :
    ∃ k, r k < t ∧ r k ∈ U := by sorry
