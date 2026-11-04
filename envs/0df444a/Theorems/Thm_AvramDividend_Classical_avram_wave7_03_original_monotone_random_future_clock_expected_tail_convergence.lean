-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_monotone_random_future_clock_expected_tail_convergence
-- name    : AvramDividend.Classical.avram_wave7_03_original_monotone_random_future_clock_expected_tail_convergence
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T07:57:02.120773+00:00
-- url     : https://prove2.me/theorems/fd03da97-226c-48aa-bd69-023d5fba8ee4
-- title:
--   Original expected ENNReal dividend tails vanish along increasing random clocks from a.e. tail vanishing
-- statement:
--   For the original spectrally negative Lévy process X under its actual law P and the original stochastic dividend measure, let measurable lower clocks T_n increase on P-almost every sample path. Assume genuine strictly future ENNReal Stieltjes payout after T_n tends to zero on almost every original path. If the full original dividendValue is finite, then the expected strict-future ENNReal payout after each random clock tends to zero too. This is an exact source-measure dominated convergence theorem for random localisation sequences, with no surrogate clock/sample space or change to the right-limit dividend atoms.
-- source:
--   Pinned Mathlib lintegral_tendsto_of_tendsto_of_antitone; Proved original strict-future random-clock kernel measurability ea1c2561; pathwise antitonicity by lintegral_mono_set; finite domination by the canonical dividendValue. No Open theorem imports.

import Mathlib.MeasureTheory.Integral.Lebesgue.Sub
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_strict_future_random_clock_cash_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_monotone_random_future_clock_expected_tail_convergence
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (q : ℝ)
    (T : ℕ → Ω → ℝ)
    (hTm : ∀ n, Measurable (T n))
    (hTmono : ∀ᵐ ω ∂P, Monotone (fun n => T n ω))
    (hPoint : ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ =>
        ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Ioi (T n ω),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))
        atTop (𝓝 (0 : ℝ≥0∞)))
    (hFinite : dividendValue X q x D < ⊤) :
    Tendsto (fun n : ℕ =>
      ∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Ioi (T n ω),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P)
      atTop (𝓝 (0 : ℝ≥0∞)) := by sorry
