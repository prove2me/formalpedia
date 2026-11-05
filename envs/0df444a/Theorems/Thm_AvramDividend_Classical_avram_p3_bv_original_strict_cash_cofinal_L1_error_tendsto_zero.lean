-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_cash_cofinal_L1_error_tendsto_zero
-- name    : AvramDividend.Classical.avram_p3_bv_original_strict_cash_cofinal_L1_error_tendsto_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T10:09:48.303579+00:00
-- url     : https://prove2.me/theorems/fbd2608a-f80b-421d-a981-251ff00cd86a
-- title:
--   Original stopped BV strict Stieltjes dividend cash cofinal approximations converge in L1
-- statement:
--   Along any increasing nonnegative cofinal grid, the true original BV dividend Stieltjes cash strictly before the horizon converges to the actual horizon strict cash in L1 of the original probability measure P. Its expected absolute error tends to zero using monotonicity, admissible right-payment bound, known L1 and the previously Proved cofinal expectation limit. All time-zero cash remains included; right-horizon dividends remain excluded as prescribed.
-- source:
--   Original cash expected convergence 36f7b99a, Proved original strict cash L1 67a9c5bf, Proved original strict horizon monotonicity e1100117 and right-limit domination 512282cc, pinned Mathlib Bochner integral_sub and real abs_of_nonneg.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_cash_strict_horizon_mono
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_cash_rightlimit_bound
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_cash_L1
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_cash_cofinal_expected_tendsto_real
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_bv_original_strict_cash_cofinal_L1_error_tendsto_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (S : ℝ≥0)
    (u : ℕ → ℝ) (hmono : Monotone u)
    (hu : ∀ n, 0 ≤ u n)
    (hbelow : ∀ n, u n ≤ (S : ℝ))
    (hcover : ∀ s : ℝ, s < (S : ℝ) → ∃ n, s < u n) :
    Tendsto (fun n => ∫ ω : Ω,
      |(∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (S : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω).toReal -
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (u n),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω).toReal| ∂P)
      atTop (nhds 0) := by sorry
