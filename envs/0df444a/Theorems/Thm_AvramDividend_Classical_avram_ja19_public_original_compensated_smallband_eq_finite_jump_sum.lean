-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja19_public_original_compensated_smallband_eq_finite_jump_sum
-- name    : AvramDividend.Classical.avram_ja19_public_original_compensated_smallband_eq_finite_jump_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T13:04:34.401801+00:00
-- url     : https://prove2.me/theorems/d6ed76f6-6754-4714-9f45-ba199ab79c29
-- title:
--   Public original finite-band compensated jump source equals finite sum minus deterministic compensator
-- statement:
--   The original intrinsic finite-band compensated negative-jump source is, pathwise, exactly the finite sum of all original process negative jumps in the cutoff mark band (0,T] minus T times the original Levy mark compensator. Reprove the original-space source decomposition publicly because the previously Proved equivalent declaration 1c1d4731 has private visibility and cannot be imported by public targets. No auxiliary process or large-jump first moment.
-- source:
--   J-A19 public reproof of original physical finite-activity jump-source identity

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja19_public_original_compensated_smallband_eq_finite_jump_sum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n : ℕ) (T : ℝ≥0) (ω : Ω) :
    let j : ℝ≥0 → ℝ := fun u =>
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
    ∃ F : Finset ℝ≥0,
      (∀ u : ℝ≥0, u ∈ F ↔ 0 < u ∧ u ≤ T ∧ -1 < j u ∧
        j u ≤ -(1 / ((n : ℝ) + 1))) ∧
      avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω =
        (∑ u ∈ F, j u) -
          (T : ℝ) * (∫ z in Ioc (-1 : ℝ)
            (-(1 / ((n : ℝ) + 1))), z ∂X.ν) := by sorry
