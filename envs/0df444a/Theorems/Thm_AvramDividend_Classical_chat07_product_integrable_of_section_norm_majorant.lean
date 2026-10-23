-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat07_product_integrable_of_section_norm_majorant
-- name    : AvramDividend.Classical.chat07_product_integrable_of_section_norm_majorant
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T07:27:12.362235+00:00
-- url     : https://prove2.me/theorems/7918d923-49d9-43a0-a39d-26b1c6dc1447
-- title:
--   Fubini product-integrability from integrable section-norm envelope
-- statement:
--   Suppose a jointly almost-everywhere strongly measurable kernel has integrable sections for almost every jump magnitude. If its section L1 norm is almost everywhere strongly measurable and dominated almost everywhere by an integrable function of jump magnitude, then the full kernel is integrable with respect to the product measure. This converts the bounded-variation min(1,|y|) majorant into the integrability premise required by Fubini once the concrete generator kernel's measurability is established.

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.L1Space.Integrable

open MeasureTheory

theorem AvramDividend.Classical.chat07_product_integrable_of_section_norm_majorant
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    (K : α × β → ℝ) (g : β → ℝ)
    (hK : AEStronglyMeasurable K (μ.prod ν))
    (hsections : ∀ᵐ r ∂ν, Integrable (fun x : α => K (x,r)) μ)
    (hinner : AEStronglyMeasurable
      (fun r : β => ∫ x : α, ‖K (x,r)‖ ∂μ) ν)
    (hg : Integrable g ν)
    (hmajor : ∀ᵐ r ∂ν,
      (∫ x : α, ‖K (x,r)‖ ∂μ) ≤ g r) :
    Integrable K (μ.prod ν) := by sorry
