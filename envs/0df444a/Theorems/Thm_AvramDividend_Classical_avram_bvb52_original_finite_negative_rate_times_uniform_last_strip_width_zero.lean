-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb52_original_finite_negative_rate_times_uniform_last_strip_width_zero
-- name    : AvramDividend.Classical.avram_bvb52_original_finite_negative_rate_times_uniform_last_strip_width_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T13:01:35.237209+00:00
-- url     : https://prove2.me/theorems/a6f3ca07-5962-49ee-9654-d91000584d8d
-- title:
--   Original finite negative Levy rate times exact final physical mission uniform mesh width converges to zero
-- statement:
--   For the actual original spectrally negative Levy process with finite negative jump intensity, the original finite real negative Levy rate times the exact mission prescribed deterministic final mesh T/(n+2) tends to zero. The accepted original strict physical horizon cofinality theorem p3_grid4 proves the terminal strip shrinks, so a bounded predictable negative-mark compensator supported there has vanishing deterministic intensity error. Does not require an artificial source, clock or filtration. This is the deterministic companion to the source actual last-strip counting-measure result BVB51.
-- source:
--   Proved original p3_grid4 0071cc00 and original finite negative Levy intensity source X.ν(Iio 0).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_uniform_strict_mesh_cofinal_at_horizon
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The physical predictable negative-mark intensity of the original
finite-activity source multiplied by its prescribed last mesh width tends zero. -/

theorem AvramDividend.Classical.avram_bvb52_original_finite_negative_rate_times_uniform_last_strip_width_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ) (hT : 0 < T) :
    Tendsto (fun n : ℕ =>
      (X.ν (Iio (0 : ℝ))).toReal *
        (T / ((n : ℝ) + 2))) atTop (𝓝 (0 : ℝ)) := by sorry
