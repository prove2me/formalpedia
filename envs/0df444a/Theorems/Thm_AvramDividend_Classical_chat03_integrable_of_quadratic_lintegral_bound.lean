-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_integrable_of_quadratic_lintegral_bound
-- name    : AvramDividend.Classical.chat03_integrable_of_quadratic_lintegral_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T10:10:23.965402+00:00
-- url     : https://prove2.me/theorems/2fbeab2a-e127-41f4-957a-8e8000c6e5cd
-- title:
--   Integrability from a finite quadratic nonnegative Lebesgue integral
-- statement:
--   On a probability space, if Z is almost-everywhere strongly measurable and its quadratic nonnegative Lebesgue integral is bounded by the finite ENNReal.ofReal C, then Z is integrable. This converts the accepted Fatou bound on the limit into the integrability hypothesis needed to pass truncated expectations to full expectations.
-- source:
--   The pinned lintegral_ofReal_ne_top_iff_integrable equivalence and the separately accepted real L²-to-L¹ integrability helper.

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Topology.Order.OrderClosed
import Theorems.Thm_AvramDividend_Classical_chat03_integrable_of_integrable_real_square

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped ENNReal

theorem AvramDividend.Classical.chat03_integrable_of_quadratic_lintegral_bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (Z : Ω → ℝ) (hZm : AEStronglyMeasurable Z P) (C : ℝ)
    (hbound : (∫⁻ ω, ENNReal.ofReal ((Z ω) ^ 2) ∂P) ≤ ENNReal.ofReal C) :
    Integrable Z P := by sorry
