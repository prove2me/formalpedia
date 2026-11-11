-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18j_public_original_compensated_finsum
-- name    : AvramDividend.Classical.avram_ja18j_public_original_compensated_finsum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T23:41:52.739497+00:00
-- url     : https://prove2.me/theorems/8a238662-351d-4033-9483-ba7de76733df
-- title:
--   Public original compensated finite-band jump sum on the original sample space
-- statement:
--   Express the original finite compensated small-jump band at each time T and each original sample omega as its finite negative marked jump sum minus the deterministic Levy compensator. This exact statement previously exists privately (1c1d4731), which public target imports cannot verify. Reprove it publicly from the already Proved PUBLIC original signed band integral-to-finset identity 158e793f and the publicly available intrinsic compensated-band definition. No ownership bypass or auxiliary process.
-- source:
--   Public direct prerequisite for original right-continuous cutoff 352103fe and physical locally uniform path 9362895e.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_smallband_signed_integral_eq_finite_jump_sum
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_ja18j_public_original_compensated_finsum
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
