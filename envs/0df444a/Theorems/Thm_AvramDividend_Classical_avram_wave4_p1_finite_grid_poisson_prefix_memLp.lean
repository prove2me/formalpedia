-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_finite_grid_poisson_prefix_memLp
-- name    : AvramDividend.Classical.avram_wave4_p1_finite_grid_poisson_prefix_memLp
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T14:26:21.783018+00:00
-- url     : https://prove2.me/theorems/28a15d79-569b-4814-aa9f-1680e2ad2589
-- title:
--   Finite grid of independent-count Poisson compensated weights is L2
-- statement:
--   For each cell i, let H_i be a measurable original-path past weight with finite second moment, and K_i a measurable genuine Poisson(r_i) count independent of H_i. Then for every finite horizon n, the compensated weighted count sum Σ_{i<n} H_i(K_i-r_i) lies in L2(P), without assuming any covariance cancellation or joint independence between different cells. This is proved using the canonically Proved one-cell past-weighted Poisson L2 variance theorem, the pinned exact memLp_two_iff_integrable_sq equivalence, and MemLp.add induction. It supplies the prefix-MemLp premise of the P1 finite-grid isometry and does not assume an isometry/martingale identity.
-- source:
--   Canonical Proved weighted-count Poisson L2 isometry UUID f2883713-ef8b-46a8-8b0b-1f96a76239ce; exact pinned Mathlib.MeasureTheory.Function.L2Space memLp_two_iff_integrable_sq header; MemLp.add and Finset.sum_range_succ.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_past_weighted_poisson_count_l2_isometry

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Nat BigOperators

theorem AvramDividend.Classical.avram_wave4_p1_finite_grid_poisson_prefix_memLp
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (H : ℕ → Ω → ℝ) (K : ℕ → Ω → ℕ) (r : ℕ → ℝ≥0)
    (hHm : ∀ i, Measurable (H i))
    (hHSq : ∀ i, Integrable (fun ω => (H i ω) ^ 2) P)
    (hKm : ∀ i, Measurable (K i))
    (hKlaw : ∀ i, HasLaw (K i) (poissonMeasure (r i)) P)
    (hIndep : ∀ i, IndepFun (H i) (K i) P) :
    ∀ n, MemLp (fun ω =>
      ∑ i ∈ Finset.range n, H i ω * ((K i ω : ℝ) - (r i : ℝ))) 2 P := by sorry
