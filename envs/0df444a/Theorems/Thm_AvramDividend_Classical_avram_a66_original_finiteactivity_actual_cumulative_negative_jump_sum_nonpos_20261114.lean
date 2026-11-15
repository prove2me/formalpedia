-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a66_original_finiteactivity_actual_cumulative_negative_jump_sum_nonpos_20261114
-- name    : AvramDividend.Classical.avram_a66_original_finiteactivity_actual_cumulative_negative_jump_sum_nonpos_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T12:36:47.30794+00:00
-- url     : https://prove2.me/theorems/593bf79a-4a27-4cd2-b8e3-432925a10bc9
-- title:
--   Original finite-activity actual physical negative-jump accumulated sum is nonpositive on each horizon on one conull event
-- statement:
--   For the genuine original finite-negative-activity spectrally negative Lévy source, the finite causal sum of its actual negative jump marks through any observation time is always nonpositive on one common probability-one event.
-- source:
--   Proved A30 original finite physical marked jump support and A65 pathwise nonpositive mark theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a30_original_finiteactivity_physical_jump_sum_cadlag_on_each_horizon_20261114
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Original finite-activity actual jump accumulation is nonpositive at each time on a common conull event. -/

theorem AvramDividend.Classical.avram_a66_original_finiteactivity_actual_cumulative_negative_jump_sum_nonpos_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      let j : ℝ≥0 → ℝ := fun u =>
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
      ∃ S : Finset ℝ≥0,
        (∀ u, u ∈ S ↔ 0 < u ∧ u ≤ T ∧ j u ≠ 0) ∧
        (∀ t : ℝ≥0, t ≤ T →
          (∑ u ∈ S, if u ≤ t then j u else 0) ≤ 0) := by sorry
