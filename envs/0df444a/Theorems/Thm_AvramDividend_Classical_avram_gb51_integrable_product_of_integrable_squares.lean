-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gb51_integrable_product_of_integrable_squares
-- name    : AvramDividend.Classical.avram_gb51_integrable_product_of_integrable_squares
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T11:27:01.107209+00:00
-- url     : https://prove2.me/theorems/2293c156-e535-4844-ae31-9d5584f32a86
-- title:
--   Integrable measurable real squares imply integrability of their mixed product
-- statement:
--   For two measurable real random variables whose squares are integrable, their mixed product is integrable. This supplies the off-diagonal integrability in Gaussian quadratic cell orthogonality gb33 from the proved gb34 L2 estimate.
-- source:
--   Apply the elementary bound |fg|≤f²+g² and monotonicity of integrability; needed for gb33 original Gaussian quadratic cells.

import Mathlib
open MeasureTheory
noncomputable section

theorem AvramDividend.Classical.avram_gb51_integrable_product_of_integrable_squares
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f g : Ω → ℝ)
    (hfmeas : Measurable f) (hgmeas : Measurable g)
    (hf : Integrable (fun ω => f ω ^ 2) μ)
    (hg : Integrable (fun ω => g ω ^ 2) μ) :
    Integrable (fun ω => f ω * g ω) μ := by sorry
