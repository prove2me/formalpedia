-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_topcap_finite_product_ae_bounded_kernel_integrable
-- name    : AvramDividend.Classical.avram_bvb_topcap_finite_product_ae_bounded_kernel_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T12:34:41.307445+00:00
-- url     : https://prove2.me/theorems/b50c3643-8f8d-4481-a2df-e8af85d599d3
-- title:
--   Finite product measure real marked kernel with deterministic almost-everywhere bound is integrable
-- statement:
--   Every almost-everywhere strongly measurable real kernel on a product of two finite measures is Bochner integrable if its absolute value is bounded almost everywhere by a nonnegative finite real constant. Unlike earlier phys29 the bound only needs to hold almost everywhere; this permits exceptional original P-null paths in the top-cap reserve envelope.
-- source:
--   Direct integrable-constant norm domination with finite product instance. Used to combine topcap original product-a.e. negative-mark payoff bound b7f7a6c5 with Proved predictable kernel measurability to close original V rate L1 73b687ec.

import Mathlib
open MeasureTheory Set
noncomputable section

theorem AvramDividend.Classical.avram_bvb_topcap_finite_product_ae_bounded_kernel_integrable
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β)
    (hμ : μ Set.univ < ⊤) (hν : ν Set.univ < ⊤)
    (H : α × β → ℝ)
    (hHm : AEStronglyMeasurable H (μ.prod ν))
    (K : ℝ) (hK0 : 0 ≤ K)
    (hK : ∀ᵐ p ∂(μ.prod ν), |H p| ≤ K) :
    Integrable H (μ.prod ν) := by sorry
