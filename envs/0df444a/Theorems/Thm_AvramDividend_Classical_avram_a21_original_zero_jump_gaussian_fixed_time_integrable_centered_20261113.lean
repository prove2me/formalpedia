-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a21_original_zero_jump_gaussian_fixed_time_integrable_centered_20261113
-- name    : AvramDividend.Classical.avram_a21_original_zero_jump_gaussian_fixed_time_integrable_centered_20261113
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T10:17:06.707194+00:00
-- url     : https://prove2.me/theorems/082b7410-dbdc-4b56-b1cf-b1c7999fb400
-- title:
--   Source pure Gaussian zero-jump centered fixed-time process is L1 and mean zero
-- statement:
--   For every pure Gaussian zero-jump Lévy process on its ORIGINAL probability space, drift-centred fixed-time position is integrable and has zero mean. This follows directly from the Proved source conditional centred Gaussian increment theorem at s=0 and the pinned Mathlib integral_condExp identity. It is the needed source Gaussian centring input for the strictly positive-time omitted-tail orthogonality route.
-- source:
--   Proved Gaussian deterministic increment conditional mean 61f27325, original source X_zero field, pinned Mathlib integral_condExp and integral_congr_ae.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a21_original_zero_jump_gaussian_fixed_time_integrable_centered_20261113
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (Y : SpectrallyNegativeLevy P 𝓕) (hν : Y.ν = 0)
    (t : ℝ≥0) :
    Integrable (fun ω => Y.X t ω - (t : ℝ) * Y.c) P ∧
      (∫ ω, Y.X t ω - (t : ℝ) * Y.c ∂P) = 0 := by sorry
