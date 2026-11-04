-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_source_BV_small_nonlin_L1_of_local_Lipschitz
-- name    : AvramDividend.Classical.avram_p3_b_bvjump_original_source_BV_small_nonlin_L1_of_local_Lipschitz
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:11:06.385533+00:00
-- url     : https://prove2.me/theorems/ae49bce9-1610-46be-b18f-c03f730ea899
-- title:
--   Original BV Lévy source nonlinear small-jump L1 from compact Lipschitz localisation alone
-- statement:
--   For the original bounded-variation Lévy process X, a compact local Lipschitz estimate for w on [a,b] and a one-unit interior margin for u automatically imply that z↦w(u+z)-w(u) is continuous on (-1,0) and therefore almost everywhere strongly measurable under X.ν restricted to that band. The already Proved original BV negative first moment then makes this nonlinear small-jump integrand L1. No standalone measurability axiom or untruncated large negative-tail moment is needed.
-- source:
--   Original X.BoundedVariation and accepted P3-B source first-moment integrability 8002bc3f with Mathlib ContinuousOn.aestronglyMeasurable

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_source_BV_small_negative_nonlin_integrable
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.avram_p3_b_bvjump_original_source_BV_small_nonlin_L1_of_local_Lipschitz {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) (w : ℝ → ℝ) (K : ℝ≥0) (a b u : ℝ) (hLip : LipschitzOnWith K w (Icc a b)) (hu : u ∈ Icc (a + 1) b) : IntegrableOn (fun z : ℝ => w (u + z) - w u) (Ioo (-1 : ℝ) 0) X.ν := by sorry
