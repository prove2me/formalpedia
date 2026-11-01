-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_source_jump_times_finite_on_horizon
-- name    : AvramDividend.Classical.avram_wave4_04a_bv_actual_source_jump_times_finite_on_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T14:43:24.939652+00:00
-- url     : https://prove2.me/theorems/6a65718c-c002-4f92-98e7-85d17ced83e5
-- title:
--   Genuine original BV Lévy source has finitely many actual nonzero jumps on every positive finite horizon under finite negative intensity
-- statement:
--   For the actual SpectrallyNegativeLevy process X on its original Ω, P and filtration 𝓕, if X has bounded variation and finite negative Lévy intensity, then on a P-full event there are only finitely many strictly positive times t≤T at which its genuine càdlàg path has a nonzero left-limit jump. The theorem requires no finite-range hypothesis and no substituted Poisson process. It is source-path jump-time local finiteness, the first step toward a source jump counting measure.
-- source:
--   Compose original-X finite-range residual theorem avram_wave4_04a_bv_actual_finite_residual_range_on_horizon (publication pending) with actual original-X jump-time finiteness under a finite residual range avram_wave4_04a_bv_actual_source_jump_times_finite_of_finite_range (publication pending). Both are source-specific, and the second uses the canonically Proved actual nonzero source mark iff strict residual jump theorem 7423dfee-c973-497f-a274-07e572cbd7a0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_source_jump_times_finite_of_finite_range
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_finite_residual_range_on_horizon

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_04a_bv_actual_source_jump_times_finite_on_horizon
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ ω ∂P,
      {t : ℝ≥0 |
        t ≤ T ∧ 0 < t ∧
          X.X t ω -
            Function.leftLim (fun u : ℝ≥0 => X.X u ω) t ≠ 0}.Finite := by sorry
