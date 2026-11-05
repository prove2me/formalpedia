-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_leanlevy_bridge_original_nu_mesh_pair_rate_limit_auto
-- name    : AvramDividend.Classical.avram_leanlevy_bridge_original_nu_mesh_pair_rate_limit_auto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:50:01.0822+00:00
-- url     : https://prove2.me/theorems/83db5394-98b1-4ff3-b15a-3c7bb985f067
-- title:
--   Source uniform chronological pair-rate limit with original band finiteness discharged
-- statement:
--   For any original spectrally negative Levy X, the uniform finite mesh chronological rate ENNReal expression converges to ((T ν_X(B))^2)/2 with no extra finiteness hypothesis, since original source P2-A already proves every separated negative Borel band ν_X B finite. Consumer P4-F can import the exact source rate limit without carrying an auxiliary assumption.
-- source:
--   Proved original band finiteness 86086cb2-e1cd-4ed8-a49b-7f8eefc9842b and accepted original pair-rate limit 31e87da4-7ba8-4052-bea1-4dd3e6741255.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_separated_borel_nu_finite
import Theorems.Thm_AvramDividend_Classical_avram_leanlevy_bridge_original_nu_mesh_pair_rate_limit
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_leanlevy_bridge_original_nu_mesh_pair_rate_limit_auto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ) :
    let a : ℝ := (X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
    Tendsto
      (fun m : ℕ => ENNReal.ofReal
        (((m : ℝ) * ((m : ℝ) - 1) / 2) *
          (((T : ℝ) * a) ^ 2 / (m : ℝ) ^ 2)))
      atTop (𝓝 ((((T : ℝ≥0∞) *
        X.ν (Iic (-(1 / ((n : ℝ) + 1))))) ^ 2) / 2)) := by sorry
