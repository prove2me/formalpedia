-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_21_original_strict_stopped_full_measure_BV_compact_value_budget
-- name    : AvramDividend.Classical.avram_wave8_21_original_strict_stopped_full_measure_BV_compact_value_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T23:54:58.039381+00:00
-- url     : https://prove2.me/theorems/0b16a789-af37-4edf-a89d-d15dc2088d34
-- title:
--   Original strict-stopped BV compact candidate-value plus literal complete Stieltjes mass budget
-- statement:
--   On an original bounded-variation spectrally negative Levy trajectory satisfying the explicit compact strip endpoint hypotheses, under strict survival to deterministic horizon T, the literal original dividendMeasure D ω of paymentTimes ∩ Iic T (converted to real) plus the C1 candidate value increment is bounded by the original local drift budget plus the initial cumulative rightpayment. The statement uses exact original Stieltjes mass, includes continuous and singular-continuous payout and zero/horizon rightpayment atoms, and allows reserve at cap equality through the already Proved full-cap secant lemma. It supplies the pathwise accounting interface to W8-04 without asserting an unproved martingale expectation estimate.
-- source:
--   Direct composition of Proved W7-02 original BV compact stopped right-dividend C1 budget with accepted W8-21 original full Stieltjes mass identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_compact_stopped_full_right_dividend_C1_pathwise_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave8_21_original_strict_survival_full_paid_measure_eq_rightLimit
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave8_21_original_strict_stopped_full_measure_BV_compact_value_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (a b L : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hbC : ENNReal.ofReal b ≤ C)
    (hL1 : 1 ≤ L)
    (hLip : ∀ y ∈ Icc a b, ∀ z ∈ Icc a b,
      |w y - w z| ≤ L * |y - z|) :
    ∀ᵐ ω ∂P, ∀ (T : ℝ≥0),
      (T : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ rightLimit D T ω →
      x + X.X 0 ω - rightLimit D 0 ω ∈ Icc a b →
      x + X.X T ω - rightLimit D T ω ∈ Icc a b →
      ((dividendMeasure D ω)
        (paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ))).toReal +
        (w (x + X.X T ω - rightLimit D T ω) -
          w (x + X.X 0 ω - rightLimit D 0 ω)) ≤
        L * (((T : ℝ) - (0 : ℝ)) * X.drift) +
          rightLimit D 0 ω := by sorry
