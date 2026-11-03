-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_zero_or_strict_preruin_paymentTimes_closed_signed_nonpos
-- name    : AvramDividend.Classical.avram_wave6_06_original_zero_or_strict_preruin_paymentTimes_closed_signed_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T10:33:42.315824+00:00
-- url     : https://prove2.me/theorems/75563ed6-01a1-4556-8af6-17e56512c4f4
-- title:
--   Genuine original paymentTimes all-cap signed Stieltjes budget at zero or strictly before ruin
-- statement:
--   For the actual original Lévy process and any admissible left-continuous dividend D, the exact paymentTimes(σ)∩Iic τ discounted complete Stieltjes dividend measure plus the cap-linear V change to the true post-dividend source reserve is ≤0 whenever the clock τ is either zero (even if ruin occurs at time zero) or strictly before ruin. All caps C including zero/infinite are allowed. The zero-time right dividend atom is retained. This is deterministic source signed cash, not an Ito chain rule at positive ruin-crossing times.
-- source:
--   Avram Proposition 4(i), Eq. (5.11)–(5.13); Proved b7f6754b and ec132215, with source-definition direct time-zero paymentTimes case.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_05_any_cap_original_closed_full_stieltjes_signed_nonpos
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_strict_preruin_random_clock_paymentTimes_eq_Icc
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_06_original_zero_or_strict_preruin_paymentTimes_closed_signed_nonpos
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
    (hPre : τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω) :
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal +
      (V (x + X.X (τ ω) ω - rightLimit D (τ ω) ω) -
       V (x + X.X (τ ω) ω)) ≤ 0 := by sorry
