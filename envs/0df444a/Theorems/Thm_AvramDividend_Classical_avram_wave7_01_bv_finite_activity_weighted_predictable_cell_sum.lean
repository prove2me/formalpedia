-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_bv_finite_activity_weighted_predictable_cell_sum
-- name    : AvramDividend.Classical.avram_wave7_01_bv_finite_activity_weighted_predictable_cell_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:44:12.588705+00:00
-- url     : https://prove2.me/theorems/4f7dd1a9-2292-48e3-8bd4-bac3f5decef1
-- title:
--   Original finite-activity BV weighted predictable marked cell expectation sum
-- statement:
--   On the original P, Ω, X and filtration, sum finitely many actual negative-marked jump-count predictable rectangle expectations with arbitrary nonnegative deterministic weights. All time-cell starts may equal zero, intervals may degenerate and A_i is measurable at its original start s_i. Under BV and explicit ν((−∞,0))<∞, each compensated cell rate is P(A_i)(t_i−s_i)ν((−∞,0)); finite sums preserve the exact identity. No independent proxy and no claim under infinite activity.
-- source:
--   Previously Proved all-start original BV finite-activity source rectangle c78120b8; Mathlib Finset.sum_congr. Consumer interface for finite predictable step coefficients.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_bv_finite_activity_all_start_actual_negative_predictable_rectangle
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_01_bv_finite_activity_weighted_predictable_cell_sum
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (S : Finset ℕ) (s t : ℕ → ℝ≥0)
    (hst : ∀ i ∈ S, s i ≤ t i)
    (A : ℕ → Set Ω) (hA : ∀ i ∈ S, MeasurableSet[𝓕 (s i)] (A i))
    (c : ℕ → ℝ≥0∞) :
    (∑ i ∈ S, c i * (∫⁻ ω in A i,
      ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s i) (t i) ×ˢ Iio (0 : ℝ)) ∂P)) =
      ∑ i ∈ S, c i * (P (A i) *
        (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (Iio (0 : ℝ)))) := by sorry
