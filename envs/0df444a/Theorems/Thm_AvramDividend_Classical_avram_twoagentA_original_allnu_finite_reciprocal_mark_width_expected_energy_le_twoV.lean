-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_twoagentA_original_allnu_finite_reciprocal_mark_width_expected_energy_le_twoV
-- name    : AvramDividend.Classical.avram_twoagentA_original_allnu_finite_reciprocal_mark_width_expected_energy_le_twoV
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T13:53:33.853152+00:00
-- url     : https://prove2.me/theorems/6680c5a2-8eaa-4d32-8570-ef5a2de46421
-- title:
--   Original infinite-activity reciprocal mark count width budget controlled by quadratic Levy energy
-- statement:
--   For any original spectrally negative Lévy process X, finite horizon T and reciprocal negative mark annulus n≤m, prove the weighted expected count-width sum ∑ δ_i (T ν(A_i)) is bounded by two times T times the actual original Lévy quadratic energy on the corresponding band. No global finite negative ν assumption. This quantifies the physical full signed-jump versus reciprocal quantizer approximation needed for original compensated Itô source.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_twoagentA_shared_negative_reciprocal_endpoint_monotone
import Theorems.Thm_AvramDividend_Classical_avram_twoagentA_shared_original_finite_negative_band_facts
import Theorems.Thm_AvramDividend_Classical_avram_twoagentA_shared_original_quadratic_annulus_energy_sum
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_nu_quadratic_real_energy

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_twoagentA_original_allnu_finite_reciprocal_mark_width_expected_energy_le_twoV
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (n m : ℕ) (hnm : n ≤ m) :
    let B : Set ℝ :=
      Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
    let A : ℕ → Set ℝ := fun i =>
      Ioc (-(1 / ((i : ℝ) + 1))) (-(1 / ((i : ℝ) + 2)))
    let r : ℕ → ℝ := fun i =>
      ((T : ℝ≥0∞) * X.ν (A i)).toReal
    let δ : ℕ → ℝ := fun i =>
      1 / ((i : ℝ) + 1) - 1 / ((i : ℝ) + 2)
    let V : ℝ := (T : ℝ) * (∫ z in B, z ^ 2 ∂X.ν)
    (∑ i ∈ Finset.Ico n m, δ i * r i) ≤ 2 * V := by sorry
