-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_unrestricted_integrable_signed_stieltjes_tail_tendsto_zero
-- name    : AvramDividend.Classical.avram_wave7_03_original_unrestricted_integrable_signed_stieltjes_tail_tendsto_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:46:50.229201+00:00
-- url     : https://prove2.me/theorems/c94fa5f6-8405-461b-95d3-ed4584d5931a
-- title:
--   Actual original unrestricted integrable real signed Stieltjes strict pre-ruin tails vanish at infinity
-- statement:
--   Fix the actual original spectrally negative Levy process, original dividend D, a path ω and any real discount q. If the genuine unrestricted real discounted Stieltjes factor is IntegrableOn the exact source paymentTimes(ruinTime X x D ω) against the exact dividendMeasure D ω, then the real signed Stieltjes integral on precisely paymentTimes(ruinTime)∩Ioi n tends to zero as n→∞. The proof applies a remotely Proved signed dominated-convergence theorem to the original source Stieltjes measure restricted to the exact full pre-ruin set, and uses measurable-set restriction composition to recover the identical original tail domain. This retains the initial right-limit atom and all continuous/jump payments in the original full domain; the tail excludes time zero naturally. Finiteness is an explicit genuine integrability premise, not inferred from a totalised real integral when the ENNReal cash is infinite.
-- source:
--   Accepted generic integrable signed antitone measurable set tails theorem 8eac15a0; pinned MeasureTheory.integral_indicator and MeasureTheory.Measure.restrict_restrict; exact source dividendMeasure/paymentTimes.

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04_integrable_signed_measurable_antitone_set_tails_tendsto_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_unrestricted_integrable_signed_stieltjes_tail_tendsto_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (ω : Ω) (q : ℝ)
    (hInt : IntegrableOn (fun t : ℝ => Real.exp (-(q * t)))
      (paymentTimes (ruinTime X x D ω)) (dividendMeasure D ω)) :
    Tendsto (fun n : ℕ =>
      ∫ t in paymentTimes (ruinTime X x D ω) ∩ Ioi (n : ℝ),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω))
      atTop (𝓝 0) := by sorry
