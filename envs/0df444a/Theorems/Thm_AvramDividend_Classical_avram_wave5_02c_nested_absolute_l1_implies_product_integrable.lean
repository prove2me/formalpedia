-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_02c_nested_absolute_l1_implies_product_integrable
-- name    : AvramDividend.Classical.avram_wave5_02c_nested_absolute_l1_implies_product_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:47:35.34403+00:00
-- url     : https://prove2.me/theorems/2364cbd8-1ac2-49db-937e-4084f847271c
-- title:
--   Finite predictable negative-mark absolute energy gives integrability for the marked product measure
-- statement:
--   For a measurable real marked kernel on two measurable spaces, finite iterated absolute L1 energy with respect to the second measure and then the first implies genuine Bochner integrability against their product measure, assuming the second measure is s-finite. Used to turn the actual ruin-stopped Taylor intensity energy into the integrability hypothesis of the original right-continuous stopped-compensation interface.
-- source:
--   Basic measure-theoretic Fubini/Tonelli bridge specialised to Chat03 original-source nonlinear Taylor remainder; exact pinned Mathlib lemmas lintegral_prod and hasFiniteIntegral_iff_norm.

import Mathlib
open MeasureTheory

theorem AvramDividend.Classical.avram_wave5_02c_nested_absolute_l1_implies_product_integrable
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite ν]
    (F : α × β → ℝ)
    (hF : Measurable F)
    (hE : (∫⁻ a, ∫⁻ b, ENNReal.ofReal (|F (a,b)|) ∂ν ∂μ) < ⊤) :
    Integrable F (μ.prod ν) := by sorry
