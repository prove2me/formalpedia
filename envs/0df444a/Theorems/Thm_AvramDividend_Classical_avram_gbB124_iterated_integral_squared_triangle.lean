-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB124_iterated_integral_squared_triangle
-- name    : AvramDividend.Classical.avram_gbB124_iterated_integral_squared_triangle
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T00:27:46.55621+00:00
-- url     : https://prove2.me/theorems/5c7ff48e-93f9-478b-b85f-4e1bca3578f8
-- title:
--   Iterated-integral L2 squared triangle bound under explicit integrability
-- statement:
--   For any two measure spaces and three measurable squared-error kernels with integrable inner squared errors and integrable outer energy functions, the iterated squared distance from f to g is at most twice the sum of squared distances from f to h and h to g. The elementary pointwise inequality is integrated twice. This is the analytic estimate required for the original finite-cap B121 physical energy bound, with measurability and integrability exposed as explicit separate obligations.

import Mathlib
open MeasureTheory Filter Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB124_iterated_integral_squared_triangle
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β)
    (f g h : α → β → ℝ)
    (hfgIn : ∀ a, Integrable
      (fun b => (f a b - g a b) ^ 2) ν)
    (hfhIn : ∀ a, Integrable
      (fun b => (f a b - h a b) ^ 2) ν)
    (hhgIn : ∀ a, Integrable
      (fun b => (h a b - g a b) ^ 2) ν)
    (hfgOut : Integrable
      (fun a => ∫ b, (f a b - g a b) ^ 2 ∂ν) μ)
    (hfhOut : Integrable
      (fun a => ∫ b, (f a b - h a b) ^ 2 ∂ν) μ)
    (hhgOut : Integrable
      (fun a => ∫ b, (h a b - g a b) ^ 2 ∂ν) μ) :
    (∫ a, (∫ b, (f a b - g a b) ^ 2 ∂ν) ∂μ) ≤
      2 * ((∫ a, (∫ b, (f a b - h a b) ^ 2 ∂ν) ∂μ) +
        (∫ a, (∫ b, (h a b - g a b) ^ 2 ∂ν) ∂μ)) := by sorry
