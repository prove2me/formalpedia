-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_05_generic_bv_stieltjes_Ioc_product_of_fubini
-- name    : AvramDividend.Classical.avram_wave6_05_generic_bv_stieltjes_Ioc_product_of_fubini
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T07:23:58.45286+00:00
-- url     : https://prove2.me/theorems/27aa4ca4-a994-4db9-9952-84e703002d1c
-- title:
--   Half-open Stieltjes product identity from exact BV Fubini exchange
-- statement:
--   For two bounded-variation real paths, the half-open Stieltjes integration-by-parts identity follows algebraically from the exact Fubini equality of the two increment integrals. The BV integrability of both one-sided limits is provided by an independently Proved generic theorem, and the endpoint increments come from the Ioc vector-measure formula. This separates the genuine Fubini exchange from straightforward integration linearity and endpoint algebra.
-- source:
--   Apply the proven generic BV integrability child to justify subtracting constant integrands on (a,b]. Evaluate constant vector-measure integrals via VectorMeasure.setIntegral_const and BoundedVariationOn.vectorMeasure_Ioc. Substitute the Fubini premise and use commutative real algebra to obtain the exact Ioc product identity. The Fubini premise remains an explicit genuine analytic assumption here.

import Mathlib
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure
import Theorems.Thm_AvramDividend_Classical_avram_wave6_05_generic_bv_vector_stieltjes_interval_integrability
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave6_05_generic_bv_stieltjes_Ioc_product_of_fubini
    (f g : ℝ≥0 → ℝ)
    (hf : BoundedVariationOn f Set.univ)
    (hg : BoundedVariationOn g Set.univ)
    (a b : ℝ≥0) (hab : a ≤ b)
    (hFubini :
      (∫ᵛ t in Ioc a b, (Function.rightLim g t - Function.rightLim g a) ∂<• hf.vectorMeasure) =
      (∫ᵛ t in Ioc a b, (Function.rightLim f b - Function.leftLim f t) ∂• hg.vectorMeasure)) :
    (∫ᵛ t in Ioc a b, Function.leftLim f t ∂• hg.vectorMeasure) =
      Function.rightLim f b • Function.rightLim g b -
      Function.rightLim f a • Function.rightLim g a -
      (∫ᵛ t in Ioc a b, Function.rightLim g t ∂<• hf.vectorMeasure) := by sorry
