-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_05_generic_bv_vector_stieltjes_interval_integrability
-- name    : AvramDividend.Classical.avram_wave6_05_generic_bv_vector_stieltjes_interval_integrability
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T06:45:22.620329+00:00
-- url     : https://prove2.me/theorems/c826e956-9916-4f20-ad2e-9fe891500af9
-- title:
--   BV left/right limits are vector-Stieltjes integrable on a half-open interval and its left singleton
-- statement:
--   For any two globally bounded-variation real paths on nonnegative time, their left and right limits are vector-measure integrable against the corresponding Stieltjes vector measures on a finite half-open interval and its left singleton. This exposes the exact four integrability premises required by pinned Mathlib's setIntegral_union when connecting the closed and half-open Stieltjes identities. The theorem is a genuine analytic BV integrability obligation; it is not an integration-by-parts product rule. It should be proved by variation domination, boundedness and measurability of regulated BV limits, including at time zero.
-- source:
--   Establish that each bounded-variation Stieltjes vector measure has finite total variation on the prescribed interval and singleton, by domination from the variation construction. Show the left/right regulated limits of the opposite BV path are strongly measurable and bounded there. Apply the finite-measure bounded-function integrability criterion, reducing vector-measure IntegrableOn to integrability for the restricted variation measure. This is presently an Open dependency, not an established compilation result.

import Mathlib

open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave6_05_generic_bv_vector_stieltjes_interval_integrability
    (f g : ℝ≥0 → ℝ)
    (hf : BoundedVariationOn f Set.univ)
    (hg : BoundedVariationOn g Set.univ)
    (a b : ℝ≥0) (hab : a ≤ b) :
    hg.vectorMeasure.IntegrableOn (Function.leftLim f) (Ioc a b) ∧
    hg.vectorMeasure.IntegrableOn (Function.leftLim f) ({a} : Set ℝ≥0) ∧
    hf.vectorMeasure.IntegrableOn (Function.rightLim g) (Ioc a b) ∧
    hf.vectorMeasure.IntegrableOn (Function.rightLim g) ({a} : Set ℝ≥0) := by sorry
