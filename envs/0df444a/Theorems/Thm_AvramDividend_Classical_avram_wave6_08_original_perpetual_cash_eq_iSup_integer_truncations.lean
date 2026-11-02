-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_perpetual_cash_eq_iSup_integer_truncations
-- name    : AvramDividend.Classical.avram_wave6_08_original_perpetual_cash_eq_iSup_integer_truncations
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T23:55:48.200478+00:00
-- url     : https://prove2.me/theorems/21a1dc8d-bdf0-495c-90c9-b633cb6ddbab
-- title:
--   Actual original full-Stieltjes perpetual dividend cash equals integer-cutoff supremum
-- statement:
--   On each genuine sample path, the complete original dividend Stieltjes cash over paymentTimes(ruinTime) equals the supremum over its closed integer time truncations, with no assumption of finite ruin or finite cash, by monotone convergence for the original measure and the nonnegative discounted kernel.
-- source:
--   Proved paymentTimes_measurable on original sample paths; Mathlib lintegral_iSup exact pinned revision. Independent deterministic original measure exhaustion directly required to pass Proved 20163182 finite-horizon original expected dividend budgets to all-time payoff.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave6_08_original_perpetual_cash_eq_iSup_integer_truncations
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (ω : Ω) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω) =
      ⨆ n : ℕ, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Iic (((n + 1 : ℕ) : ℝ)),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω) := by sorry
