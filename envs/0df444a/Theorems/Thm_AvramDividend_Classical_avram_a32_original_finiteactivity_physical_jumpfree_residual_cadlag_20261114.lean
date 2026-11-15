-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a32_original_finiteactivity_physical_jumpfree_residual_cadlag_20261114
-- name    : AvramDividend.Classical.avram_a32_original_finiteactivity_physical_jumpfree_residual_cadlag_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:48:55.95257+00:00
-- url     : https://prove2.me/theorems/1ab03ca7-6630-4066-a5eb-5bbbfd77b6aa
-- title:
--   Original finite-activity physical marked-jump removal leaves a pathwise càdlàg jumpfree residual on every finite horizon
-- statement:
--   For an original finite-activity spectrally negative Lévy process, on one conull event and for every finite horizon the causal finite sum of actual physical jump marks can be subtracted from X, leaving a right-continuous path with left limits and no jumps at positive times up to that horizon.
-- source:
--   Proved source finite-horizon support and A30 exact marked-jump matching plus original Lévy path cadlag properties.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Removing actual finite-activity jumps from the original source leaves a right-continuous, left-limited jumpfree residual on each horizon. -/

theorem AvramDividend.Classical.avram_a32_original_finiteactivity_physical_jumpfree_residual_cadlag_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      let f : ℝ≥0 → ℝ := fun t => X.X t ω
      let j : ℝ≥0 → ℝ := fun t => f t - Function.leftLim f t
      ∃ S : Finset ℝ≥0,
        (∀ t, t ∈ S ↔ 0 < t ∧ t ≤ T ∧ j t ≠ 0) ∧
        (∀ t : ℝ≥0,
          ContinuousWithinAt
            (fun v => f v - ∑ u ∈ S, if u ≤ v then j u else 0)
            (Ici t) t) ∧
        (∀ t : ℝ≥0, 0 < t →
          Tendsto
            (fun v => f v - ∑ u ∈ S, if u ≤ v then j u else 0)
            (𝓝[<] t)
            (𝓝 (Function.leftLim f t -
              ∑ u ∈ S, if u < t then j u else 0))) ∧
        (∀ t : ℝ≥0, 0 < t → t ≤ T →
          f t - (∑ u ∈ S, if u ≤ t then j u else 0) =
          Function.leftLim f t -
            (∑ u ∈ S, if u < t then j u else 0)) := by sorry
