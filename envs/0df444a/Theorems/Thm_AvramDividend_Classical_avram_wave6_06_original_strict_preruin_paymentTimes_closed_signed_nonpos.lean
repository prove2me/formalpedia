-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_strict_preruin_paymentTimes_closed_signed_nonpos
-- name    : AvramDividend.Classical.avram_wave6_06_original_strict_preruin_paymentTimes_closed_signed_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T10:26:26.168186+00:00
-- url     : https://prove2.me/theorems/d141d535-7758-4853-9e4f-3c0d795bf735
-- title:
--   Original strict pre-ruin stopped paymentTimes: complete signed Stieltjes cash dominated by actual cap-linear value loss
-- statement:
--   For the original spectrally negative Lévy X and genuinely admissible left-continuous D, at any strictly pre-ruin random clock and any cap C including zero and infinity, the actual discounted complete Stieltjes dividend paid over paymentTimes(ruinTime) up to the clock, added to the cap-linear verification-value drop from the original uncontrolled source reserve to its post-dividend reserve, is nonpositive. Includes right atoms at zero, simultaneous jumps, diffuse and singular-continuous dividends. Uses no mixed source Itô identity; positive ruin-crossing cells remain outside its hypotheses.
-- source:
--   Avram–Palmowski–Pistorius Proposition 4(i), Eq. (5.11)–(5.13). Integrates canonical Proved b7f6754b original any-cap full signed Stieltjes estimate with canonical Proved ec132215 exact original strict pre-ruin paymentTimes random-clock domain equality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_05_any_cap_original_closed_full_stieltjes_signed_nonpos
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_strict_preruin_random_clock_paymentTimes_eq_Icc
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_06_original_strict_preruin_paymentTimes_closed_signed_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (q : ℝ) (hq : 0 ≤ q) (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z → ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (τ : Ω → ℝ≥0)
    (hStrict : (τ ω : ℝ≥0∞) < ruinTime X x D ω) :
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal +
      (V (x + X.X (τ ω) ω - rightLimit D (τ ω) ω) -
       V (x + X.X (τ ω) ω)) ≤ 0 := by sorry
