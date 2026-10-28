-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_futurePath_boundedReward_lintegral_finite
-- name    : AvramDividend.Classical.levy_futurePath_boundedReward_lintegral_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T13:28:20.260629+00:00
-- url     : https://prove2.me/theorems/086aed37-bf94-4708-be1b-41eaa48c1840
-- title:
--   Bounded Lévy future-path reward has finite expectation under an integrable constant bound
-- statement:
--   A bounded nonnegative measurable path reward has finite expectation under the full Lévy path law whenever its uniform bound is integrable under the underlying measure. Adaptedness gives path-map measurability and pushforward conservation of total mass.
-- source:
--   Eliminates the redundant hRewardFinite assumption in the finite-stopping scalar strong Markov bridge, advancing AvramDividend.Classical.levy_strongMarkov_shiftedPath_indep_stoppedEvent and child 79978d61-9d1f-4b20-b8a5-114797a8e380.

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_futurePath_boundedReward_lintegral_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (g : (ℝ≥0 → ℝ) → ℝ≥0∞)
    (C : ℝ≥0∞) (hbound : ∀ y, g y ≤ C)
    (hfin : (∫⁻ _ : Ω, C ∂P) ≠ ∞) :
    (∫⁻ y, g y ∂(Measure.map
      (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) P)) ≠ ∞ := by
  sorry
