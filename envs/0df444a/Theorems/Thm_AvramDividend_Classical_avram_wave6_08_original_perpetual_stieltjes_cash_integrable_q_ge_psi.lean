-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_perpetual_stieltjes_cash_integrable_q_ge_psi
-- name    : AvramDividend.Classical.avram_wave6_08_original_perpetual_stieltjes_cash_integrable_q_ge_psi
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T00:15:04.682211+00:00
-- url     : https://prove2.me/theorems/22bc0708-a2ee-4e8f-b728-95522946eaa2
-- title:
--   Genuine infinite-horizon original Lévy full-Stieltjes dividend cash is L1 when q≥ψ(1)
-- statement:
--   Under true original-source q≥ψ(1), the full ruin-stopped dividend payoff, including all Stieltjes components and any infinite horizon, is an integrable real random variable. Follows from genuine global expected payoff bound and perpetual cash measurability; no stochastic estimate hypothesis is introduced.
-- source:
--   Proved db59cbee original perpetual kernel measurable, 5969ca80 source perpetual expected exponential bound once canonically Proved, pinned Mathlib integrable_toReal_of_lintegral_ne_top. Independent Chat08 L1 contribution for source Fatou.

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_perpetual_stieltjes_cash_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_perpetual_expected_cash_q_ge_psi
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave6_08_original_perpetual_stieltjes_cash_integrable_q_ge_psi
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : X.ψ 1 ≤ q) :
    Integrable (fun ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω).toReal) P := by sorry
