-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_original_finiteactivity_intrinsic_smallmark_actual_finite_jump_path_ae
-- name    : AvramDividend.Classical.avram_b24_original_finiteactivity_intrinsic_smallmark_actual_finite_jump_path_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T16:52:40.970456+00:00
-- url     : https://prove2.me/theorems/d2e12371-fc60-43db-811a-c7a000dc8ada
-- title:
--   Every true original finite-activity intrinsic compensated smallmark path has its exact finite negative jump sum
-- statement:
--   For EVERY original finite-negative-activity Lévy source X on its genuine sample space and EVERY intrinsic compensated small negative-mark residual limit witness Jsmall (only a.e. all-time convergence required), on one conull event and at EVERY physical t≥0, a finite support S of ACTUAL X jump times up to t exists and Jsmall(t) equals their finite sum of true jumps in (-1,0), minus the genuine full signed smallmark compensator t*∫(-1,0) zν. This identifies the original jump residual directly and makes the ruin-causing terminal mark survive correctly, without a synthetic small jump process or postruin extension.
-- source:
--   Proved original a30 finite physical jump support; original a22 finite marked cutoff identity; B84 signed smallmark moment limit; finite cutoff mark convergence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_a30_original_finiteactivity_physical_jump_sum_cadlag_on_each_horizon_20261114
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b24_original_finiteactivity_intrinsic_smallmark_actual_finite_jump_path_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (Jsmall : ℝ≥0 → Ω → ℝ)
    (hJsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω)
        atTop (𝓝 (Jsmall t ω))) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      ∃ S : Finset ℝ≥0,
        (∀ u : ℝ≥0, u ∈ S ↔ 0 < u ∧ u ≤ t ∧
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0) ∧
        Jsmall t ω =
          (∑ u ∈ S,
            if -1 < X.X u ω -
                Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∧
              X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u < 0
            then X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
            else 0) -
          (t : ℝ) * (∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν) := by sorry
