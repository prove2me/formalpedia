-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_09_original_admissible_zero_start_zero_horizon_cash_eq_zero
-- name    : AvramDividend.Classical.avram_wave7_09_original_admissible_zero_start_zero_horizon_cash_eq_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:57:23.359671+00:00
-- url     : https://prove2.me/theorems/c96bf020-0ba5-4af5-88ec-d63e094899fb
-- title:
--   Admissible zero-start original dividend control has zero full Stieltjes cash at horizon zero for any cap
-- statement:
--   For any original spectrally negative Lévy source process, cap C, source-admissible zero-start dividend control, discount q, possibly zero or infinite ruin cut-off σ and sample ω, the complete discounted Stieltjes cash on paymentTimes σ restricted to horizon T=0 is identically zero. The result uses the exact initial atom identity and the intrinsic admissibility right-limit condition. It complements, without contradicting, the positive finite-horizon zero-cap BV payout exhibited by the finite-activity reflected strategy.
-- source:
--   Canonical Proved truncated_dividend_payoff_at_zero_eq_initial_atom 50183965 and avram_wave6_08_any_cap_original_zero_start_right_dividend_vanishes fed78910. Original dividendMeasure and paymentTimes. Independent of BV, of hxc, and of C.

import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_09_original_admissible_zero_start_zero_horizon_cash_eq_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X 0 C D)
    (q : ℝ) (σ : ℝ≥0∞) (ω : Ω) :
    (∫⁻ t in paymentTimes σ ∩ Iic (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) = 0 := by sorry
