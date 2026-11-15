-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a30_original_finiteactivity_physical_jump_sum_cadlag_on_each_horizon_20261114
-- name    : AvramDividend.Classical.avram_a30_original_finiteactivity_physical_jump_sum_cadlag_on_each_horizon_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:24:40.753202+00:00
-- url     : https://prove2.me/theorems/12644677-f6be-4151-962e-7d39c91f22af
-- title:
--   Original finite-activity physical negative-jump accumulator is cadlag and matches each true source jump on every finite horizon on one conull event
-- statement:
--   On one original source conull event, each finite horizon has a finite marked-jump support with an associated causal pathwise càdlàg jump accumulator whose exact left jumps agree with every actual physical Lévy jump on the horizon.
-- source:
--   Proved original finite activity jump support 1e50b68a and A30 finite step-sum cadlag and exact jump identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed12_original_finite_activity_jump_time_support_finite_ae
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Every finite-activity physical source path has a finite cadlag jump accumulator with exactly the original jumps on each compact horizon. -/

theorem AvramDividend.Classical.avram_a30_original_finiteactivity_physical_jump_sum_cadlag_on_each_horizon_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      let j : ℝ≥0 → ℝ := fun u =>
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
      ∃ S : Finset ℝ≥0,
        (∀ u, u ∈ S ↔ 0 < u ∧ u ≤ T ∧ j u ≠ 0) ∧
        (∀ t : ℝ≥0,
          ContinuousWithinAt
            (fun v : ℝ≥0 => ∑ u ∈ S, if u ≤ v then j u else 0)
            (Ici t) t) ∧
        (∀ t : ℝ≥0, 0 < t →
          Tendsto
            (fun v : ℝ≥0 => ∑ u ∈ S, if u ≤ v then j u else 0)
            (𝓝[<] t)
            (𝓝 (∑ u ∈ S, if u < t then j u else 0))) ∧
        (∀ t : ℝ≥0, 0 < t → t ≤ T →
          (∑ u ∈ S, if u ≤ t then j u else 0) -
          (∑ u ∈ S, if u < t then j u else 0) = j t) := by sorry
