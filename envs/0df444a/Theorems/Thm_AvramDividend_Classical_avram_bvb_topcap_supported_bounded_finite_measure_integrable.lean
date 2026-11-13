-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_topcap_supported_bounded_finite_measure_integrable
-- name    : AvramDividend.Classical.avram_bvb_topcap_supported_bounded_finite_measure_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T11:10:15.792669+00:00
-- url     : https://prove2.me/theorems/fbed8e23-68a7-42aa-ac71-b5941187783c
-- title:
--   Bounded measurable real integrand with finite measurable support is integrable
-- statement:
--   Any real-valued measurable function vanishing outside a measurable set of finite measure and uniformly bounded on that set is Bochner integrable. This applies to finite-activity stopped marked-jump measures.
-- source:
--   Finite-support domination by indicator constant and integrability domination. Enables topcap original physical negative-mark fibre L1.

import Mathlib
open MeasureTheory Set
noncomputable section

theorem AvramDividend.Classical.avram_bvb_topcap_supported_bounded_finite_measure_integrable
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (S : Set α) (hS : MeasurableSet S) (hSfinite : μ S < ⊤)
    (f : α → ℝ) (hf : Measurable f)
    (hSupport : ∀ a, a ∉ S → f a = 0)
    (K : ℝ) (hK : 0 ≤ K)
    (hBound : ∀ a ∈ S, |f a| ≤ K) :
    Integrable f μ := by sorry
