-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_shiftedIncrements_rightContinuous
-- name    : AvramDividend.Classical.levy_shiftedIncrements_rightContinuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T19:14:06.651001+00:00
-- url     : https://prove2.me/theorems/12789e6e-1ce2-4c3a-9401-20e60e4a61c8
-- title:
--   Deterministically shifted Lévy increments preserve right continuity at every future time
-- statement:
--   For a spectrally negative Lévy process, every sample path shifted by a fixed nonnegative clock u and rebased to zero remains right-continuous. Compose original right-continuity at u+t with the continuous translation s↦u+s and subtract the constant X(u). This supplies a pathwise regularity hypothesis to the generic running-supremum right-continuity theorem without imposing a shifted-process Lévy law.
-- source:
--   Exact hνneg bridge for strong-Markov barrier child 79978d61-9d1f-4b20-b8a5-114797a8e380, via reflectedPath_dividendMeasure_zero_nonpositive prepared helper and Proved runningSup_right_continuous_of_right_continuous f0c2320c. No scale-function parameters.

import Mathlib.Topology.Instances.NNReal.Lemmas
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_shiftedIncrements_rightContinuous
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (u : ℝ≥0) :
    ∀ t : ℝ≥0,
      ContinuousWithinAt
        (fun s : ℝ≥0 => X.X (u + s) ω - X.X u ω)
        (Set.Ici t) t := by
  sorry
