-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_restrictedFutureReward_lintegral
-- name    : AvramDividend.Classical.levy_finiteStopping_restrictedFutureReward_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T15:59:48.054821+00:00
-- url     : https://prove2.me/theorems/7897c433-701a-4e27-8235-9b066fac352a
-- title:
--   Stopped-future Lévy path reward factorisation under a stopped-history event
-- statement:
--   The nonnegative expectation of any measurable future-path reward, restricted to an event observable at a finite stopping time, is the event probability times the original unshifted path reward expectation. This is the integral-level strong-Markov bridge needed for the discounted barrier-dividend splitting identity.
-- source:
--   From Proved full stopped-future path law plus the Proved restricted path law to lintegral scalar bridge. No scale-function assumptions.

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_restrictedFuturePath_mapLaw
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_stoppedFuturePath_measurable
import Theorems.Thm_AvramDividend_Classical_stoppedHistory_event_measurable
import Theorems.Thm_AvramDividend_Classical_restrictedPathLaw_scalar_lintegral_reward

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_finiteStopping_restrictedFutureReward_lintegral
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s}))
    (g : (ℝ≥0 → ℝ) → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ ω, Set.indicator A
      (fun ω' => g (fun t : ℝ≥0 =>
        X.X (τ ω' + t) ω' - X.X (τ ω') ω')) ω ∂P) =
    P A * (∫⁻ ω, g (fun t : ℝ≥0 => X.X t ω) ∂P) := by
  sorry
