-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_truncated_residual_source_jump_series
-- name    : AvramDividend.Classical.avram_p4_h_gaussian_original_truncated_residual_source_jump_series
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T00:10:39.804762+00:00
-- url     : https://prove2.me/theorems/7c80f340-cc1f-4197-bf5d-c4240aff927d
-- title:
--   Actual finite-cutoff Gaussian residual is the same-process jump-time series minus original Levy compensator
-- statement:
--   On the original probability space and original X path, express its finite-cutoff residual R^n exactly as X.X minus physical drift, the actual sum of finite-band negative jumps, the same-source deterministic ν compensation and the actual large-jump term. This is a pathwise finite-band identity only; no continuity, L2 limit, martingale or bracket is assumed.
-- source:
--   Previously published original residual and intrinsic small-band definitions plus Proved P4-H exact original signed band integral to source jump tsum theorem 79505e86-97d7-40f8-8e89-2b42beaae958.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_smallband_signed_integral_eq_intrinsic_tsum
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical
noncomputable section

theorem AvramDividend.Classical.avram_p4_h_gaussian_original_truncated_residual_source_jump_series
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n : ℕ) (t : ℝ≥0) (ω : Ω) :
    let j : ℝ≥0 → ℝ := fun u =>
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
    let E : Set (ℝ≥0 × ℝ) :=
      Ioc (0 : ℝ≥0) t ×ˢ Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1)))
    avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω =
      X.X t ω - (t : ℝ) * X.c -
        ((∑' u : ℝ≥0, if 0 < u ∧ j u ≠ 0 then
            E.indicator (fun p : ℝ≥0 × ℝ => p.2) (u, j u) else 0) -
          (t : ℝ) * (∫ z in Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))), z ∂X.ν)) -
        avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω := by sorry
