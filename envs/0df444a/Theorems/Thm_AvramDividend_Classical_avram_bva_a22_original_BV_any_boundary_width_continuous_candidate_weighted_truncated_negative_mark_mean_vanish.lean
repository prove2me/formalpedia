-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_BV_any_boundary_width_continuous_candidate_weighted_truncated_negative_mark_mean_vanish
-- name    : AvramDividend.Classical.avram_bva_a22_original_BV_any_boundary_width_continuous_candidate_weighted_truncated_negative_mark_mean_vanish
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T08:54:32.893978+00:00
-- url     : https://prove2.me/theorems/084e07d6-d19d-4161-8310-06810663aa9c
-- title:
--   Original BV near-zero negative-mark boundary budget weighted by a continuous candidate vanishes without needing w(0)=0
-- statement:
--   For the genuine original BV spectrally negative Levy source X, any HJB candidate w continuous on the nonnegative reserve half-line, and any prescribed positive shrinking spatial boundary widths epsilon(n) <=1, the original negative Levy truncated first-moment boundary intensity multiplied by the actual candidate w(epsilon(n)) tends to zero. This allows w(0)>0 as in the original positive-ruin dividend problem. The Proved exact negative mark first-moment integral converges to zero, while continuity gives w(epsilon(n)) -> w(0); their product tends to zero. No finite jump activity, fast spatial grid diagonal or global generator L1 is assumed. Connecting this scalar boundary layer to original stopped time/space occupation remains a separate source obligation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_BV_any_spatial_boundary_width_truncated_negative_mark_first_moment_vanish
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_a22_original_BV_any_boundary_width_continuous_candidate_weighted_truncated_negative_mark_mean_vanish
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici (0 : ℝ)))
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n ∧ ε n ≤ 1)
    (hεlim : Tendsto ε atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun n =>
      (∫ z in Iio (0 : ℝ), min (ε n) (-z) ∂X.ν) * w (ε n))
      atTop (𝓝 (0 : ℝ)) := by sorry
