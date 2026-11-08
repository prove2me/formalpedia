-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gen18_product_affine_geometric_not_integrable
-- name    : AvramDividend.Classical.avram_gen18_product_affine_geometric_not_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T19:01:02.992098+00:00
-- url     : https://prove2.me/theorems/4927c10f-4575-4397-ba52-39401194b95a
-- title:
--   The actual singular affine HJB deficit remains nonintegrable after an independent finite probability factor
-- statement:
--   An independent probabilistic factor cannot turn the nonintegrable dyadic affine HJB profile into an integrable product-space variable. This is the precise product-space bridge needed when the geometric reserve index is sampled independently of a genuine Levy process. It does not assume or construct the original process.
-- source:
--   Accepted affine geometric HJB nonintegrability theorem 687f069c-4a07-44d5-b043-842cdbbb9596 and pinned Mathlib Integrable.comp_snd_iff, finite probability measure.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gen17_actual_affine_hjb_geometric_not_integrable
open MeasureTheory ProbabilityTheory
noncomputable section

theorem AvramDividend.Classical.avram_gen18_product_affine_geometric_not_integrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (p : unitInterval) (hp : p ≠ 0) (hhalf : (p : ℝ) = 1 / 2) : ¬ Integrable (fun z : Ω × ℕ => (3 : ℝ) + 1 / (16 * ((2 : ℝ) ^ z.2) ^ 2) - 4 * Real.sqrt (1 / (16 * ((2 : ℝ) ^ z.2) ^ 2)) - 2 / Real.sqrt (1 / (16 * ((2 : ℝ) ^ z.2) ^ 2))) (μ.prod (geometricMeasure p)) := by sorry
