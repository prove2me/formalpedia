-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a36_original_intrinsic_gaussian_limit_continuous_on_each_horizon_20261114
-- name    : AvramDividend.Classical.avram_a36_original_intrinsic_gaussian_limit_continuous_on_each_horizon_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T09:15:16.513608+00:00
-- url     : https://prove2.me/theorems/f9626a76-eb31-4592-aaee-9cdd6b79da0d
-- title:
--   Original finite-negative-activity intrinsic Gaussian residual limit has physically continuous sample paths on every compact horizon on one conull event
-- statement:
--   Every actual original finite-activity spectrally negative Lévy source intrinsic Gaussian cutoff limit R has continuous real-valued sample paths on every finite time horizon, simultaneously on one event of probability one in the original source space. The continuity comes directly from physical marked-jump removal and the exact original source decomposition.
-- source:
--   Proved A33 original finite-horizon jumpremoved source continuity, A35 exact original Gaussian source identity, and A35 genuine finite-support mark series localisation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a36_original_intrinsic_gaussian_limit_continuous_on_each_horizon_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (𝓝 (R t ω))) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      ContinuousOn (fun t : ℝ≥0 => R t ω) (Iic T) := by sorry
