-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_05_generic_bv_stieltjes_Icc_Ioc_endpoint_split
-- name    : AvramDividend.Classical.avram_wave6_05_generic_bv_stieltjes_Icc_Ioc_endpoint_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T06:30:50.850491+00:00
-- url     : https://prove2.me/theorems/b7dd7a83-dfaf-44ed-8401-bfa30e2e6fe2
-- title:
--   Exact open-closed endpoint corrections for two bounded-variation vector Stieltjes integrals
-- statement:
--   Under explicit integrability assumptions on the singleton and half-open interval, the closed-interval left-limit vector Stieltjes integral equals its half-open counterpart plus f^-(a) times the right-left atom of g. Dually, the right-limit g integral against the vector measure of f picks up the right-left atom of f times g^+(a). The result follows from genuinely disjoint vector-measure integration and exact singleton masses, including a=0. It does not assume or claim a general integration-by-parts product rule. In the exponential-discount application the atom of f is zero, which isolates the sole g endpoint correction.
-- source:
--   The pinned Mathlib setIntegral_union lemma applies to the disjoint measurable partition [a,b]={a}∪(a,b] under the four explicit integrability hypotheses. The pinned VectorMeasure.integral_singleton lemma evaluates each singleton integral, and BoundedVariationOn.vectorMeasure_singleton computes its mass as the difference of right and left limits. Rearrange the two sums by associativity and commutativity.

import Mathlib

open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave6_05_generic_bv_stieltjes_Icc_Ioc_endpoint_split
    (f g : ℝ≥0 → ℝ)
    (hf : BoundedVariationOn f Set.univ)
    (hg : BoundedVariationOn g Set.univ)
    (a b : ℝ≥0) (hab : a ≤ b)
    (hflIoc : hg.vectorMeasure.IntegrableOn (Function.leftLim f) (Ioc a b))
    (hflAt : hg.vectorMeasure.IntegrableOn (Function.leftLim f) ({a} : Set ℝ≥0))
    (hgrIoc : hf.vectorMeasure.IntegrableOn (Function.rightLim g) (Ioc a b))
    (hgrAt : hf.vectorMeasure.IntegrableOn (Function.rightLim g) ({a} : Set ℝ≥0)) :
    ((∫ᵛ t in Icc a b, Function.leftLim f t ∂• hg.vectorMeasure) =
        (∫ᵛ t in Ioc a b, Function.leftLim f t ∂• hg.vectorMeasure) +
          Function.leftLim f a • (Function.rightLim g a - Function.leftLim g a)) ∧
    ((∫ᵛ t in Icc a b, Function.rightLim g t ∂<• hf.vectorMeasure) =
        (∫ᵛ t in Ioc a b, Function.rightLim g t ∂<• hf.vectorMeasure) +
          (Function.rightLim f a - Function.leftLim f a) • Function.rightLim g a) := by sorry
