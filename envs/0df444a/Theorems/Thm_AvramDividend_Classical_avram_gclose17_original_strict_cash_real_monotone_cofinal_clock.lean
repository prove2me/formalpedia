-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gclose17_original_strict_cash_real_monotone_cofinal_clock
-- name    : AvramDividend.Classical.avram_gclose17_original_strict_cash_real_monotone_cofinal_clock
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T23:01:28.950574+00:00
-- url     : https://prove2.me/theorems/cea9d467-bf4f-4598-8bbe-2c4e2a4590e7
-- title:
--   Exact original strict discounted dividend cash converges along any increasing cofinal physical cutoff
-- statement:
--   For one original admissible dividend path, an arbitrary increasing sequence of real time cutoffs lying below a finite positive horizon and cofinal from below recovers the exact strictly-before-horizon discounted Stieltjes cash in real numbers. The original source closed cash finiteness justifies ENNReal-to-real conversion. This generalises fixed-width shrinkage to path-dependent cofinal cutoff sequences used by the Gaussian exit-clock Fatou passage, and never includes the right-payment atom at the limit horizon.
-- source:
--   Physical original dividendMeasure.withDensity, continuity from below for measurable strict payment-time sets, real convergence after the original closed-cap finiteness bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gclose17_original_strict_cash_real_monotone_cofinal_clock
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D) (ω : Ω)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ) (hT : 0 < T)
    (u : ℕ → ℝ) (hmono : Monotone u)
    (hbelow : ∀ n, u n ≤ T)
    (hcover : ∀ s : ℝ, s < T → ∃ n, s < u n) :
    Tendsto (fun n : ℕ =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (u n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal)
      atTop
      (𝓝 ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal)) := by sorry
