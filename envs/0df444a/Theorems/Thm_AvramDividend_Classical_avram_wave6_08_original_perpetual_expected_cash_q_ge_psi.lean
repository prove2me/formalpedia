-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_perpetual_expected_cash_q_ge_psi
-- name    : AvramDividend.Classical.avram_wave6_08_original_perpetual_expected_cash_q_ge_psi
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T23:54:02.694225+00:00
-- url     : https://prove2.me/theorems/5969ca80-a5eb-4242-aaf1-c2a7aa559bdb
-- title:
--   Perpetual original Lévy expected Stieltjes cash bounded by exp(x) when q≥ψ(1)
-- statement:
--   For an arbitrary capped actual spectrally negative Lévy dividend strategy D, whenever the real discount q dominates the true source exponent ψ(1), the expected complete original Stieltjes reward over every genuine pre-ruin payment time, including infinite horizon, is at most exp(x). Prove by original finite-horizon budget, cofinal nonnegative closed intervals, original payment kernel measurability and monotone convergence; no stochastic representation or estimator is assumed.
-- source:
--   Proved 20163182-6fe0-45b6-b2a1-445c2fd35c24 finite-horizon actual stopped expected exponential payoff, Proved 2d478c7d-9d35-4371-a220-d9fd063c4852 bounded inclusive-clock cash measurability, Proved db59cbee-4085-43eb-a6bf-b5ec11efe6b4 perpetual cash measurable, pinned Mathlib lintegral_iSup. This is a further nonconditional source-rate reward theorem independent of Chat06 mixed Lévy Itô–Meyer assembly.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_actual_source_closedHorizon_stopped_fullStieltjes_cash_q_ge_psi
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_random_upper_clock_complete_stieltjes_cash_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_perpetual_stieltjes_cash_measurable
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave6_08_original_perpetual_expected_cash_q_ge_psi
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : X.ψ 1 ≤ q) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω ∂P) ≤
      ENNReal.ofReal (Real.exp x) := by sorry
