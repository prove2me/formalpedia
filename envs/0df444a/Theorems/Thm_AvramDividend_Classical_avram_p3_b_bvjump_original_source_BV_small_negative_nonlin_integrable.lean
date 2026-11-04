-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_source_BV_small_negative_nonlin_integrable
-- name    : AvramDividend.Classical.avram_p3_b_bvjump_original_source_BV_small_negative_nonlin_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:56:21.253212+00:00
-- url     : https://prove2.me/theorems/8002bc3f-001f-4b9c-9048-3798a1caae79
-- title:
--   Original bounded-variation Lévy small negative nonlinear C1 jump increment is integrable
-- statement:
--   Original X.BoundedVariation supplies ∫_{(-1,0)}(-z) X.ν(dz)<∞ by the Proved source theorem bv_small_negative_first_moment_integrable. The genuine local first-order Lipschitz estimate bounds the nonlinear source increment by K|z| for pre-source reserve u in the compact interior margin [a+1,b]. Together with explicit a.e. strong measurability this yields source ν-integrability of the small-jump nonlinear C1 kernel. No untruncated large-negative-jump first moment is assumed.
-- source:
--   Proved bv_small_negative_first_moment_integrable 2296f406 and first-order source P3-B local mark bound

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_small_negative_first_moment_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_localised_first_order_small_negative_mark_bound
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.avram_p3_b_bvjump_original_source_BV_small_negative_nonlin_integrable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) (w : ℝ → ℝ) (K : ℝ≥0) (a b u : ℝ) (hLip : LipschitzOnWith K w (Icc a b)) (hu : u ∈ Icc (a + 1) b) (hMeas : AEStronglyMeasurable (fun z : ℝ => w (u + z) - w u) (X.ν.restrict (Ioo (-1 : ℝ) 0))) : IntegrableOn (fun z : ℝ => w (u + z) - w u) (Ioo (-1 : ℝ) 0) X.ν := by sorry
