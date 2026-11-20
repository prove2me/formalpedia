-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_mixed_gaussian_true_fixed_horizon_runningSup_L1
-- name    : AvramDividend.Classical.avram_f6_mixed_gaussian_true_fixed_horizon_runningSup_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T18:31:11.223+00:00
-- url     : https://prove2.me/theorems/eef65024-45d6-48af-ba73-c522f990572c
-- title:
--   True Gaussian-plus-jump Lévy runningSup at bounded physical horizon is L1
-- statement:
--   If original Lévy X has positive Gaussian scale, actual runningSup X n is integrable: proved exp(runningSup) integrability, actual measurability and nonnegative runningSup imply the L1 result. Supplies a source-backed envelope to the original finite-cap rightmesh dominated convergence HJB construction.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a391_gaussian_fixed_horizon_exp_runningSup_integrable
import Theorems.Thm_AvramDividend_Classical_levy_runningSup_joint_time_path_measurable
import Theorems.Thm_AvramDividend_Classical_runningSup_eq_rawSup_nonneg
set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_mixed_gaussian_true_fixed_horizon_runningSup_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hSigma : 0 < X.σ)
    (n : ℝ≥0) :
    Integrable (fun ω : Ω => runningSup X n ω) P := by sorry
