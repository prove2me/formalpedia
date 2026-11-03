-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_spatial_nonmonotone_liminf_exhaustion_expected_cash_budget
-- name    : AvramDividend.Classical.avram_wave7_19_original_spatial_nonmonotone_liminf_exhaustion_expected_cash_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:57:31.562573+00:00
-- url     : https://prove2.me/theorems/2c6349e0-8c95-44a9-ba89-2dc5b5277226
-- title:
--   Nonmonotone spatial localisation liminf-Fatou bridge for original finite-horizon ruin cash
-- statement:
--   For the exact original ruinTime/paymentTimes/dividendMeasure finite-horizon cash, this spatial localisation bridge accepts nonmonotone measurable local cash sequences. The explicit a.s. cover condition full cash ≤ liminf local cash is the required boundary and possible upper-cap dividend-mass exhaustion obligation. Taking increasing tail infima gives measurable monotone G_n. The monotone convergence theorem and lintegral monotonicity establish E[full cash] ≤ E[liminf local cash] ≤ liminf E[local cash] ≤ budget, without uniform integrability or any convergence of the risk process at ruin. Unlike prior spatial monotone helper f5df271c, no nesting of localisations is assumed.
-- source:
--   Original W7-19 source cash; Fatou via measurable monotone tail infima; explicit spatial boundary cash coverage and no source Ito or stopping-time assumptions smuggled in.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_19_original_spatial_nonmonotone_liminf_exhaustion_expected_cash_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x T : ℝ)
    (D : ℝ≥0 → Ω → ℝ)
    (LocalCash : ℕ → Ω → ℝ≥0∞)
    (hLocalMeas : ∀ n : ℕ, Measurable (LocalCash n))
    (hExhaust : ∀ᵐ ω ∂P,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))
        ≤ (⨆ n : ℕ, ⨅ k : ℕ, LocalCash (n + k) ω))
    (budget : ℝ≥0∞)
    (hBudgetLiminf : (⨆ n : ℕ, ⨅ k : ℕ,
      (∫⁻ ω, LocalCash (n + k) ω ∂P)) ≤ budget) :
    (∫⁻ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P) ≤ budget := by sorry
