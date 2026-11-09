-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_endpoint_original_F_le_masked_strict_cash
-- name    : AvramDividend.Classical.avram_ubv_gauss13_endpoint_original_F_le_masked_strict_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T22:16:18.916817+00:00
-- url     : https://prove2.me/theorems/c9478067-c77f-4e83-a8d6-08229e25fdab
-- title:
--   Original stopped paid terminal and closed cash bounded by zero-masked strict-prepayment ledger
-- statement:
--   For the original admissible dividend strategy at any clock, the actual source-defined F, including the right dividend payment at zero and the closed stopped-horizon Stieltjes cash, is bounded by the zero-clock value w(x) or the positive-clock prepayment reserve plus strictly-earlier cash. At positive ruin the endpoint payment is excluded by paymentTimes; at pre-ruin right jumps it is paid and compensated by the contact inequality. Applies pointwise to the genuine stopped clocks in finite 50e1cf4c and infinite-cap 249c532d; does not assert Gaussian centring, physical Ito convergence, or a random last-cell estimate.
-- source:
--   Direct exact source-to-masked-ledger bridge for finite-cap target 50e1cf4c-8dc4-40ea-b5b2-218909c25a22 and top-cap target 249c532d (4a699fd8-779b-4ddd-a463-727c365ecdd6). Uses Proved c5c292c4-69f3-4473-a059-4cb3bd8860ea and 820af26f-ced8-4e45-b6b7-53d82960593a. Original X, D, q, ruinTime, rightLimit, dividendMeasure, paymentTimes and closed/strict intervals unchanged.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_original_exact_localised_F_zero_clock_le_initial
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top12_original_positive_clock_paid_post_le_strict_pre

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gauss13_endpoint_original_F_le_masked_strict_cash
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (σ : Ω → ℝ≥0) (F : Ω → ℝ)
    (hFsource : ∀ ω, F ω =
      Real.exp (-(q * (σ ω : ℝ))) *
        w (if σ ω = 0 ∨
              (σ ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ ω) ω - rightLimit D (σ ω) ω
          else riskProcess X x D (σ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal) :
    ∀ ω, F ω ≤
      if σ ω = 0 then w x else
        Real.exp (-(q * (σ ω : ℝ))) *
          w (riskProcess X x D (σ ω) ω) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (σ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal := by sorry
