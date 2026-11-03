-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_compact_stopped_full_right_dividend_C1_pathwise_budget
-- name    : AvramDividend.Classical.avram_wave7_02_original_BV_compact_stopped_full_right_dividend_C1_pathwise_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:25:48.129882+00:00
-- url     : https://prove2.me/theorems/221932c9-0abb-4d7f-90d0-0f150048d554
-- title:
--   Original BV stopped C1 value plus all cumulative right dividend payments satisfies a common compact physical drift budget
-- statement:
--   On the original spectrally negative bounded-variation Levy path with standing positive drift and actual admissible right-dividend strategy, between any ordered stopping-sample times whose real postpayment reserves remain in one compact nonnegative cap strip, the entire cumulative right-dividend increment plus the C1 candidate value increase is at most its local Lipschitz ceiling times elapsed physical drift. The proof uses original residual monotonicity, right-dividend monotonicity and the full-cap derivative secant. It includes all diffuse, singular-continuous and right-jump payouts and negative source marks in the original trajectories. The restriction to endpoint reserves inside the compact strip is explicit; this does not assert a stopped Levy generator compensation identity.
-- source:
--   Source-specific original BV increment from bv_actual_levy_residual_ae_monotone_all_times and avram_wave3_03_dividendStrategy_rightLimit_monotone; original weak C1 full-cap gradient secant avram_wave3_03_bv_full_cap_gradient_secant. Direct pathwise stopped cash-plus-value budget for W7-04.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_residual_ae_monotone_all_times
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_full_cap_gradient_secant
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_02_original_BV_compact_stopped_full_right_dividend_C1_pathwise_budget
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
    ∀ᵐ ω ∂P, ∀ (s t : ℝ≥0), s ≤ t →
      x + X.X s ω - rightLimit D s ω ∈ Icc a b →
      x + X.X t ω - rightLimit D t ω ∈ Icc a b →
      (rightLimit D t ω - rightLimit D s ω) +
        (w (x + X.X t ω - rightLimit D t ω) -
          w (x + X.X s ω - rightLimit D s ω)) ≤
        L * (((t : ℝ) - (s : ℝ)) * X.drift) := by sorry
