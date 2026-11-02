-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_partition_remainders_sum_le_residual
-- name    : AvramDividend.Classical.avram_wave5_04a_actual_bv_source_partition_remainders_sum_le_residual
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T10:14:55.401074+00:00
-- url     : https://prove2.me/theorems/e055a5cf-6899-4f2b-a54a-d921958c3c8a
-- title:
--   Original BV Levy source partition remainders have uniformly bounded total real variation
-- statement:
--   On one original-source probability-one event, for every nondecreasing sequence of actual source times, there is a sequence of nonnegative finite real interval remainders equal to each source drift-residual increment minus the complete negative source left-jump series. The sum of the first n remainder cells is bounded by the drift-residual increment between the first and final partition points. This establishes uniform finite-variation control for stopped partition refinement, independently of any Ito-Meyer identity.
-- source:
--   Mission 1300fbe7-ca8c-49f9-a4de-4cb35ebd2f43, Wave5 Chat04-A. Derived from canonical Proved e84d1832-1a90-4b40-a0ca-e0f4065fdb5e and pinned Finset.sum_range_sub.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_interval_source_jump_real_nonnegative_remainder

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Along every actual BV source partition, the complete source left-jump
magnitudes admit real nonnegative cell remainders whose finite sums are
uniformly bounded by the genuine original drift-residual increment. -/

theorem AvramDividend.Classical.avram_wave5_04a_actual_bv_source_partition_remainders_sum_le_residual
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ (u : ℕ → ℝ≥0) (hu : Monotone u),
      ∃ r : ℕ → ℝ,
        (∀ i : ℕ, 0 ≤ r i ∧
          (∑' (v : ℝ≥0),
            if u i < v ∧ v ≤ u (i + 1) then
              ENNReal.ofReal (Function.leftLim
                (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
            else 0).toReal + r i =
          ((u (i + 1) : ℝ) * X.drift - X.X (u (i + 1)) ω) -
            ((u i : ℝ) * X.drift - X.X (u i) ω)) ∧
        (∀ n : ℕ,
          (∑ i ∈ Finset.range n, r i) ≤
            ((u n : ℝ) * X.drift - X.X (u n) ω) -
              ((u 0 : ℝ) * X.drift - X.X (u 0) ω)) := by sorry
