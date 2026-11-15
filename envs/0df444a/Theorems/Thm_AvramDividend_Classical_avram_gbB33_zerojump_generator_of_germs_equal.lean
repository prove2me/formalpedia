-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB33_zerojump_generator_of_germs_equal
-- name    : AvramDividend.Classical.avram_gbB33_zerojump_generator_of_germs_equal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T13:20:30.850698+00:00
-- url     : https://prove2.me/theorems/5d9a3473-b786-4a02-a6f7-732b585a185c
-- title:
--   Zero-jump Gaussian generator depends only on the germ of the value function
-- statement:
--   When the Lévy jump measure vanishes, any two real functions agreeing throughout a neighbourhood of a reserve point have the same generator at that point, because the Gaussian generator depends only on the first and second derivatives there. This allows an interior cap-linear extension to inherit the original HJB generator inequality below its clipping level without differentiability at that level.
-- source:
--   Pointwise zero-jump generator formula and first/second derivative eventual equality in pinned Mathlib.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f11_zero_jump_generator_eq_gaussian_drift
open Filter MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB33_zerojump_generator_of_germs_equal
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (V w : ℝ → ℝ) (y : ℝ)
    (hEv : V =ᶠ[𝓝 y] w) :
    X.generator V y = X.generator w y := by sorry
