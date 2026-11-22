-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_twoagentA_original_allnu_physical_reciprocal_expected_quantization_width_uniform_tail
-- name    : AvramDividend.Classical.avram_twoagentA_original_allnu_physical_reciprocal_expected_quantization_width_uniform_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T13:59:04.625915+00:00
-- url     : https://prove2.me/theorems/3193bbdd-59dd-40fa-8b43-a9e85a8c3c5d
-- title:
--   Original any-activity physical reciprocal mark quantisation expected width uniformly vanishes
-- statement:
--   For actual original X with arbitrary negative jump activity, the expected finite reciprocal-bin signed-mark approximation widths Σ δ_i T ν(A_i) tend uniformly to zero over all later cutoff upper indices m≥n. Derived from public original physical finite marked count width ≤2T actual ν quadratic band energy and original uniform real quadratic energy tail. Essential for identifying the physical L² reciprocal proxy limit with the true original compensated signed-mark stochastic integral.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_twoagentA_original_allnu_finite_reciprocal_mark_width_expected_energy_le_twoV
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_real_quadratic_strip_uniform_tail
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_twoagentA_original_allnu_physical_reciprocal_expected_quantization_width_uniform_tail
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) :
    let A : ℕ → Set ℝ := fun i =>
      Ioc (-(1 / ((i : ℝ) + 1))) (-(1 / ((i : ℝ) + 2)))
    let r : ℕ → ℝ := fun i =>
      ((T : ℝ≥0∞) * X.ν (A i)).toReal
    let δ : ℕ → ℝ := fun i =>
      1 / ((i : ℝ) + 1) - 1 / ((i : ℝ) + 2)
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ m : ℕ, n ≤ m →
        (∑ i ∈ Finset.Ico n m, δ i * r i) < ε := by sorry
