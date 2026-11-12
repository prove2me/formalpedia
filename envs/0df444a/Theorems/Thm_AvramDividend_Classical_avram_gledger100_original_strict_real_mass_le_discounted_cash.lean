-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger100_original_strict_real_mass_le_discounted_cash
-- name    : AvramDividend.Classical.avram_gledger100_original_strict_real_mass_le_discounted_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T12:32:45.485228+00:00
-- url     : https://prove2.me/theorems/cd9c11a6-99eb-4a4d-94ec-6c9acb625387
-- title:
--   Original strict unweighted dividend mass is bounded by a finite discounted cash envelope
-- statement:
--   For any finite strict discounted cash integral, the corresponding original unweighted Stieltjes dividend mass before a bounded time is at most exp(q times that time) times discounted cash, provided all positive pre-endpoint times are paid before ruin. This is the real-valued form of the already-proved discount-integral lower bound, useful for L1 mesh-error bounds.
-- source:
--   Real-valued mass-to-cash bridge used by original stopped Gaussian mesh errors and gledger81.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger100_original_strict_real_mass_le_discounted_cash
    (μ : Measure ℝ) (σ : ℝ≥0∞) (q : ℝ) (hq : 0 ≤ q) (b : ℝ≥0)
    (hsub : Ioo (0 : ℝ) (b : ℝ) ⊆ paymentTimes σ ∩ Iio (b : ℝ))
    (hfinite : (∫⁻ t in paymentTimes σ ∩ Iio (b : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂μ) < ⊤) :
    (μ (Ioo (0 : ℝ) (b : ℝ))).toReal ≤
      Real.exp (q * (b : ℝ)) *
        (∫⁻ t in paymentTimes σ ∩ Iio (b : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂μ).toReal := by sorry
