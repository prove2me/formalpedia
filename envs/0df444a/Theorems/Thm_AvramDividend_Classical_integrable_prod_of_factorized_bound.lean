-- Prove2me | Theorems.Thm_AvramDividend_Classical_integrable_prod_of_factorized_bound
-- name    : AvramDividend.Classical.integrable_prod_of_factorized_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T16:08:08.357636+00:00
-- url     : https://prove2.me/theorems/7c01434f-53c7-4876-add0-f5ba46deb777
-- title:
--   Global product-measure integrability under a factorised integrable majorant
-- statement:
--   A jointly almost-everywhere strongly measurable function dominated on a product measure by |g(x)| |h(y)| is integrable whenever g and h are separately integrable. This does not require a finite first measure, providing an analytic prerequisite for full-half-line Lévy generator Fubini under a weighted state envelope.
-- source:
--   Pinned Mathlib Integrable.mul_prod and Integrable.mono' applied to compensated Lévy generator Fubini.

import Mathlib

open MeasureTheory
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem integrable_prod_of_factorized_bound
    (μ ν : Measure ℝ) (f : ℝ × ℝ → ℝ) (g h : ℝ → ℝ)
    (hg : Integrable g μ) (hh : Integrable h ν)
    (hf : AEStronglyMeasurable f (μ.prod ν))
    (hdom : ∀ᵐ p ∂(μ.prod ν), ‖f p‖ ≤ |g p.1| * |h p.2|) :
    Integrable f (μ.prod ν) := by sorry

end AvramDividend.Classical
