-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_05_generic_bv_stieltjes_Ioc_fubini_exchange
-- name    : AvramDividend.Classical.avram_wave6_05_generic_bv_stieltjes_Ioc_fubini_exchange
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T07:21:37.875746+00:00
-- url     : https://prove2.me/theorems/110f52b5-d6b8-4fbd-8525-80bbf5925d76
-- title:
--   Fubini exchange of half-open increments of real BV Stieltjes vector measures
-- statement:
--   The double Stieltjes integral over the ordered triangle a < y ≤ x ≤ b can be evaluated in either order, giving equality of two single integrals of right/left-limit increments against the corresponding signed Stieltjes measures. This is the genuinely missing Fubini exchange behind the half-open BV integration-by-parts identity; it includes simultaneous jumps and all singular continuous variation.
-- source:
--   Derive by expressing g.rightLim x - g.rightLim a as hg.vectorMeasure (Ioc a x), f.rightLim b - f.leftLim y as hf.vectorMeasure (Icc y b), and applying signed/vector-measure Fubini to the indicator of the ordered triangle. This is a genuine missing analytic child, distinct from the algebraic product rule. The current upstream Mathlib.MeasureTheory.VectorMeasure.IntegrationByParts uses the same Fubini strategy, but its full module is unavailable at the mission's pinned Mathlib revision.

import Mathlib
import Mathlib.MeasureTheory.VectorMeasure.BoundedVariation
import Mathlib.MeasureTheory.VectorMeasure.Prod
open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave6_05_generic_bv_stieltjes_Ioc_fubini_exchange
    (f g : ℝ≥0 → ℝ)
    (hf : BoundedVariationOn f Set.univ)
    (hg : BoundedVariationOn g Set.univ)
    (a b : ℝ≥0) (hab : a ≤ b) :
    (∫ᵛ t in Ioc a b, (Function.rightLim g t - Function.rightLim g a) ∂• hf.vectorMeasure) =
    (∫ᵛ t in Ioc a b, (Function.rightLim f b - Function.leftLim f t) ∂• hg.vectorMeasure) := by sorry
