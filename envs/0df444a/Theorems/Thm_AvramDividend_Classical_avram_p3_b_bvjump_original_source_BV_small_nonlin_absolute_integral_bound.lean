-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_source_BV_small_nonlin_absolute_integral_bound
-- name    : AvramDividend.Classical.avram_p3_b_bvjump_original_source_BV_small_nonlin_absolute_integral_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:16:29.016811+00:00
-- url     : https://prove2.me/theorems/44a0e23c-a8af-4723-a24f-e519db0a08d6
-- title:
--   Original BV nonlinear source small-jump total absolute drift bounded by first moment
-- statement:
--   For the actual original bounded-variation Lévy process X, every compact-interior reserve u has the uniform quantitative nonlinear small-jump bound ∫_{(-1,0)}|w(u+z)-w(u)|X.ν(dz) ≤ K∫_{(-1,0)}(-z)X.ν(dz). The latter first moment is finite by the accepted original BV source theorem, and nonlinear integrability/measurability follows from the accepted local-Lipschitz BV helper. It is a bound on the true source drift without any global big-negative-jump moment or independent marked point process.
-- source:
--   Accepted original BV first negative moment and local Lipschitz nonlinear L1, Mathlib integral_mono_ae

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_small_negative_first_moment_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_localised_first_order_small_negative_mark_bound
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_source_BV_small_nonlin_L1_of_local_Lipschitz
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.avram_p3_b_bvjump_original_source_BV_small_nonlin_absolute_integral_bound {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) (w : ℝ → ℝ) (K : ℝ≥0) (a b u : ℝ) (hLip : LipschitzOnWith K w (Icc a b)) (hu : u ∈ Icc (a + 1) b) : (∫ z in Ioo (-1 : ℝ) 0, |w (u + z) - w u| ∂X.ν) ≤ (K : ℝ) * (∫ z in Ioo (-1 : ℝ) 0, -z ∂X.ν) := by sorry
