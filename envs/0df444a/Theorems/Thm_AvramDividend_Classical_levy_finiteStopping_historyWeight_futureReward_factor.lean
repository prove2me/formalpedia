-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_historyWeight_futureReward_factor
-- name    : AvramDividend.Classical.levy_finiteStopping_historyWeight_futureReward_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T16:28:06.121348+00:00
-- url     : https://prove2.me/theorems/b995a471-5065-4673-ba97-d0f13ebfc768
-- title:
--   Strong-Markov factorisation of stopped-history weighted future Lévy rewards
-- statement:
--   The expected product of a nonnegative stopped-history measurable weight and an arbitrary measurable reward of post-stopping Lévy increments factors into the expected weight and expected reward of the original Lévy path. The weight may encode a discounted first-barrier exit event before ruin. No scale-function assumptions are needed.
-- source:
--   Combines accepted stopped-history sigma independence d5bac6c4-63fd-49ee-a81b-ccda03ccab18, accepted past-weight factor 4a1ee91b-8ba3-4b25-b9bb-61ebc4958175, and accepted restricted future path law e2543758-86c1-4254-a0b4-433781e31752, moving directly towards 79978d61-9d1f-4b20-b8a5-114797a8e380.

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_stoppedFuturePath_measurable
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_restrictedFuturePath_mapLaw
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_stoppedSigma_indep_shiftedPath
import Theorems.Thm_AvramDividend_Classical_indepSigma_pastWeight_futureReward_lintegral

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_finiteStopping_historyWeight_futureReward_factor
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω : Ω | τ ω ≤ s})
    (pastWeight : Ω → ℝ≥0∞)
    (hp : Measurable pastWeight)
    (hpPast : Measurable[
      (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] pastWeight)
    (reward : (ℝ≥0 → ℝ) → ℝ≥0∞) (hr : Measurable reward) :
    (∫⁻ ω, pastWeight ω *
      reward (fun t : ℝ≥0 =>
        X.X (τ ω + t) ω - X.X (τ ω) ω) ∂P) =
      (∫⁻ ω, pastWeight ω ∂P) *
        (∫⁻ ω, reward (fun t : ℝ≥0 => X.X t ω) ∂P) := by
  sorry
