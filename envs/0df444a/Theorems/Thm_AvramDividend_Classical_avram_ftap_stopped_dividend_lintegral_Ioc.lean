-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ftap_stopped_dividend_lintegral_Ioc
-- name    : AvramDividend.Classical.avram_ftap_stopped_dividend_lintegral_Ioc
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T12:05:40.157073+00:00
-- url     : https://prove2.me/theorems/57dc92c8-5bcd-4389-be73-207a6a3be94c
-- title:
--   Pathwise stopped discounted dividend Stieltjes lintegral equals original integral on min clock
-- statement:
--   For the original dividend Stieltjes measure, restricting its measure to (0,τ] and then integrating an arbitrary nonnegative weight over (0,t] gives exactly the original weighted integral over (0,min(t,τ)]. This is an exact original dividend cash stopping identity without an assumed integration formula. Adapted from the actual stopped finite variation integral proof in Mocho Go's FTAPTheorem42/Stochastic/FiniteVariation/FiniteVariationIntegralProcessStopping.lean and its measure-restriction calculation; the origin dividend atom is deliberately excluded by both sides.
-- source:
--   https://github.com/selpoG/lean-ftap-closedness/blob/8c9c46e1b6e455f7d3069062957d4363879836ce/FTAPTheorem42/Stochastic/FiniteVariation/FiniteVariationIntegralProcessStopping.lean

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ftap_stopped_dividend_lintegral_Ioc
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (τ t : ℝ≥0) (f : ℝ → ℝ≥0∞) :
    (∫⁻ s in Ioc (0 : ℝ) (t : ℝ), f s
      ∂((dividendMeasure D ω).restrict (Ioc (0 : ℝ) (τ : ℝ)))) =
    (∫⁻ s in Ioc (0 : ℝ) ((min t τ : ℝ≥0) : ℝ),
      f s ∂(dividendMeasure D ω)) := by sorry
