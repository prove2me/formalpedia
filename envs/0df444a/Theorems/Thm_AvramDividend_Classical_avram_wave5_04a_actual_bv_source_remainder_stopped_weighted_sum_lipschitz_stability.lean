-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_remainder_stopped_weighted_sum_lipschitz_stability
-- name    : AvramDividend.Classical.avram_wave5_04a_actual_bv_source_remainder_stopped_weighted_sum_lipschitz_stability
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T12:04:52.513208+00:00
-- url     : https://prove2.me/theorems/04aefb9c-3519-47c6-b349-52bd61154dc3
-- title:
--   Actual bounded-variation source residual has sharp Lipschitz stability for stopped weighted partition sums
-- statement:
--   For the actual spectrally negative Levy source with bounded variation, almost surely its explicit canonical nondecreasing residual has finite sum contributions that are Lipschitz continuous in the sampled coefficient sequence: the absolute difference between two weighted source residual sums is bounded by the sup coefficient discrepancy M times the original residual endpoint increment. This supports C1 approximation of controlled nonlinear source terms without identifying an Ito-Meyer or Stieltjes integral.
-- source:
--   Chat04-A new original-process source finite-variation stability, derived from canonically Proved sharp weighted absolute variation bound 2496fb55-e8d1-455f-9cea-0728d868c5b9 and finite sum distributivity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_remainder_weighted_partition_absolute_variation_bound

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The genuine original BV source-residual finite-variation contribution
is Lipschitz in the sup norm of its sampled coefficient sequence. This is
the quantitative C1-approximation stability needed before Ito-Meyer. -/

theorem AvramDividend.Classical.avram_wave5_04a_actual_bv_source_remainder_stopped_weighted_sum_lipschitz_stability
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∃ R : ℝ≥0 → ℝ,
      (∀ t : ℝ≥0,
        R t = ((t : ℝ) * X.drift - X.X t ω) -
          (∑' (v : ℝ≥0),
            if 0 < v ∧ v ≤ t then
              ENNReal.ofReal (Function.leftLim
                (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
            else 0).toReal) ∧
      Monotone R ∧
      ∀ (u : ℕ → ℝ≥0) (hu : Monotone u) (n : ℕ)
        (a b : ℕ → ℝ) (M : ℝ) (hM : 0 ≤ M)
        (hab : ∀ i : ℕ, |a i - b i| ≤ M),
        |(Finset.range n).sum (fun i =>
          a i * (R (u (i + 1)) - R (u i))) -
          (Finset.range n).sum (fun i =>
            b i * (R (u (i + 1)) - R (u i)))| ≤
          M * (R (u n) - R (u 0)) := by sorry
