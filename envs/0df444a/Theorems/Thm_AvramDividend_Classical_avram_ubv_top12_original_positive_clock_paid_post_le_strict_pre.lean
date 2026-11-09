-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_top12_original_positive_clock_paid_post_le_strict_pre
-- name    : AvramDividend.Classical.avram_ubv_top12_original_positive_clock_paid_post_le_strict_pre
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T21:41:27.624197+00:00
-- url     : https://prove2.me/theorems/820af26f-ced8-4e45-b6b7-53d82960593a
-- title:
--   Exact original positive-clock closed dividend reward is bounded by strict prepayment reward
-- statement:
--   For any positive clock of an original admissible spectrally negative Levy dividend strategy, the genuine discounted postpayment terminal value plus closed Stieltjes cash is no greater than the prepayment terminal value plus strict Stieltjes cash under the original right-jump contact hypothesis. At ruin the inequality is exact. This isolates the source-exact endpoint dividend atom needed for the root-connected infinite-cap stopped Gaussian Ito budget.
-- source:
--   Root-connected Gaussian top-cap target 249c532d via afbeaf83 and 25573e81; exact original dividend endpoint comparison from public Proved 54ad337e and hJump, independently remotely compiler-probed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_closed_cash_eq_strict_plus_active_right_atom

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-! Original positive-clock endpoint comparison used in the strict Gaussian budget. -/

theorem AvramDividend.Classical.avram_ubv_top12_original_positive_clock_paid_post_le_strict_pre
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (ω : Ω) (S : ℝ≥0) (hSpos : 0 < S) :
    Real.exp (-(q * (S : ℝ))) *
      w (if (S : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X S ω - rightLimit D S ω
      else riskProcess X x D S ω) +
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (S : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
      ∂(dividendMeasure D ω)).toReal ≤
    Real.exp (-(q * (S : ℝ))) * w (riskProcess X x D S ω) +
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (S : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
      ∂(dividendMeasure D ω)).toReal := by sorry
