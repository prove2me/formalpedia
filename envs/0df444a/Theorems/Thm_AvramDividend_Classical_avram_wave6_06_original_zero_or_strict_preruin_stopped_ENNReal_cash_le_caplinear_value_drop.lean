-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_zero_or_strict_preruin_stopped_ENNReal_cash_le_caplinear_value_drop
-- name    : AvramDividend.Classical.avram_wave6_06_original_zero_or_strict_preruin_stopped_ENNReal_cash_le_caplinear_value_drop
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T10:49:46.974931+00:00
-- url     : https://prove2.me/theorems/c61d10df-d4a2-4d96-ba91-edd5af8e664e
-- title:
--   Original zero-or-preruin all-cap discounted stopped Stieltjes cash bounded in ENNReal by caplinear value loss
-- statement:
--   The genuine original discounted complete Stieltjes stopped dividend reward, at τ=0 or τ<σ and any cap including zero, is bounded directly as an ENNReal by ofReal of the cap-linear value lost to cumulative right-dividend payment at the same original source time. Finiteness of the reward follows from genuine admissible D via rightLimit D τ, not from a free integrability assumption. Covers the initial right atom even if σ=0, singular-continuous payouts, and simultaneous jumps. Does not assert the missing mixed source controlled Ito formula.
-- source:
--   Avram Proposition 4(i), source original dividendMeasure. Canonical Proved signed real stopped cash 75563ed6 and absolute source ENNReal right-limit dividend measure bound 1a006d5f; no auxiliary cash integrability assumptions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_zero_or_strict_preruin_paymentTimes_closed_signed_nonpos
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_stopped_payment_discounted_le_rightLimit
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_06_original_zero_or_strict_preruin_stopped_ENNReal_cash_le_caplinear_value_drop
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
       ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ≤
      ENNReal.ofReal
        (V (x + X.X (τ ω) ω) -
         V (x + X.X (τ ω) ω - rightLimit D (τ ω) ω)) := by sorry
