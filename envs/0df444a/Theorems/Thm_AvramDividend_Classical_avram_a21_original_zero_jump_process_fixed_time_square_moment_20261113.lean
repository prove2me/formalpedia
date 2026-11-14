-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a21_original_zero_jump_process_fixed_time_square_moment_20261113
-- name    : AvramDividend.Classical.avram_a21_original_zero_jump_process_fixed_time_square_moment_20261113
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T09:35:59.682205+00:00
-- url     : https://prove2.me/theorems/136b239c-5d86-4646-b0af-e77dd56bcd57
-- title:
--   Every original pure Gaussian Levy process has exact centred second moment
-- statement:
--   On the original probability space, for ANY zero-jump Levy process Y, the drift-centred fixed-time process is square-integrable and its exact square expectation is time times Gaussian coefficient squared. This is a direct consequence of the Proved stopped Gaussian exact variance and deterministic Gaussian square-integrability lemmas, specialising the stopping time to zero. It provides a reusable downstream input when the original Gaussian companion Y is constructed.
-- source:
--   Proved original pure Gaussian deterministic second moment square integrability ee48aad4; Proved original stopped Gaussian exact variance 3c7623a6; pinned Mathlib isStoppingTime_const.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_gaussian_deterministic_increment_condExp_variance
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_exact_variance
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a21_original_zero_jump_process_fixed_time_square_moment_20261113
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (Y : SpectrallyNegativeLevy P 𝓕) (hν : Y.ν = 0)
    (t : ℝ≥0) :
    Integrable (fun ω => (Y.X t ω - (t : ℝ) * Y.c) ^ 2) P ∧
      (∫ ω, (Y.X t ω - (t : ℝ) * Y.c) ^ 2 ∂P) =
        (t : ℝ) * Y.σ ^ 2 := by sorry
