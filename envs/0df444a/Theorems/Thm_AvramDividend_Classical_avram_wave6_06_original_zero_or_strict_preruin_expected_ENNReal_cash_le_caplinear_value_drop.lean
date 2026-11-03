-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_zero_or_strict_preruin_expected_ENNReal_cash_le_caplinear_value_drop
-- name    : AvramDividend.Classical.avram_wave6_06_original_zero_or_strict_preruin_expected_ENNReal_cash_le_caplinear_value_drop
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T10:56:29.930269+00:00
-- url     : https://prove2.me/theorems/dfdd7b1a-efd4-44c5-90d6-59ff65ace633
-- title:
--   Original stopped full-Stieltjes expected ENNReal payout bounded by expected caplinear source value loss
-- statement:
--   On any conull set of original source paths where the finite random clock is zero or strictly before original ruin, the genuine outer expectation of the complete inner source Stieltjes discounted dividend measure is at most the outer ENNReal expectation of caplinear V(x+Xτ)−V(x+Xτ−rightLimitDτ). No dividend cash integrability or source martingale assumption is needed; all caps and initial right atoms are retained. The mixed controlled Ito source identity and positive ruin crossing remain separate Open hypotheses.
-- source:
--   Avram Proposition 4(i), Eq. (5.13), conditional expectation leg. Canonical Proved c61d10df source-path ENNReal caplinear value loss dominates complete actual paymentTimes dividend cash; preserve exact same sample original X,D,τ and a.e. pre-ruin boundary.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_zero_or_strict_preruin_stopped_ENNReal_cash_le_caplinear_value_drop
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_06_original_zero_or_strict_preruin_expected_ENNReal_cash_le_caplinear_value_drop
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
    (τ : Ω → ℝ≥0)
    (hPre : ∀ᵐ ω ∂P, τ ω = 0 ∨
      (τ ω : ℝ≥0∞) < ruinTime X x D ω) :
    (∫⁻ ω,
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ∂P) ≤
    (∫⁻ ω,
      ENNReal.ofReal
        (V (x + X.X (τ ω) ω) -
         V (x + X.X (τ ω) ω - rightLimit D (τ ω) ω)) ∂P) := by sorry
