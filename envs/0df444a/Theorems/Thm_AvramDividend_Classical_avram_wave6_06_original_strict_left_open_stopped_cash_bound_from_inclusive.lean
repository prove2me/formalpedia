-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_strict_left_open_stopped_cash_bound_from_inclusive
-- name    : AvramDividend.Classical.avram_wave6_06_original_strict_left_open_stopped_cash_bound_from_inclusive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T00:17:44.661524+00:00
-- url     : https://prove2.me/theorems/3c4cb2ed-3932-4af5-8d64-247ec665e418
-- title:
--   Original strict-left positive-time stopped dividend integral bounded by full inclusive Stieltjes reward
-- statement:
--   For the actual original Levy X and admissible dividends D stopped before the original ruin, the expected discounted Stieltjes cash over (0,τ] is bounded by the already proved expected inclusive source cash over [0,τ], so the source expected budget automatically exports the user-requested open-left positive-time dividend reward even in the presence of a time-zero dividend. This is a pure monotonicity transfer of nonnegative ENNReal Stieltjes integrals and does not assert any stochastic Ito equality.
-- source:
--   Avram Proposition 4(i), original stopped dividend cash reward (0,τ] as a subreward of complete inclusive time-zero Stieltjes cash.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_06_original_strict_left_open_stopped_cash_bound_from_inclusive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 < q)
    (τ : Ω → ℝ≥0)
    (hτruin : ∀ ω, (τ ω : ℝ≥0∞) ≤ ruinTime X x D ω)
    (B : ℝ)
    (hInclusive :
      (∫⁻ ω, ∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal B) :
    (∫⁻ ω, ∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Ioc (0 : ℝ) (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal B := by sorry
