-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_05_generic_bv_stieltjes_Icc_identity_of_Ioc_and_endpoint
-- name    : AvramDividend.Classical.avram_wave6_05_generic_bv_stieltjes_Icc_identity_of_Ioc_and_endpoint
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T06:45:51.786586+00:00
-- url     : https://prove2.me/theorems/d40cd34b-aa2a-431c-af97-1e17d755dd5f
-- title:
--   A closed BV Stieltjes product identity from a half-open identity and no discount endpoint atom
-- statement:
--   Given two bounded-variation real functions on nonnegative time, explicit integrability on a half-open interval and its singleton left endpoint, equality of the left and right discount limits at that endpoint, and an existing half-open Stieltjes integration-by-parts identity, the exact closed-interval identity follows. It retains the right-endpoint product and replaces the initial right-limit product with the initial left-limit product. No product rule is asserted without the hIoc premise. This is a source-complete endpoint reduction, valid even at time zero.
-- source:
--   Import the canonically Proved singleton endpoint-splitting theorem, rewrite the two Icc integrals as Ioc integrals plus their endpoint atoms, substitute the assumed Ioc product identity, and use f.leftLim(a)=f.rightLim(a) to annihilate the f singleton atom. The remaining g singleton correction precisely changes the initial right product to the initial left product; close by ring.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave6_05_generic_bv_stieltjes_Icc_Ioc_endpoint_split

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave6_05_generic_bv_stieltjes_Icc_identity_of_Ioc_and_endpoint
    (f g : ℝ≥0 → ℝ)
    (hf : BoundedVariationOn f Set.univ)
    (hg : BoundedVariationOn g Set.univ)
    (a b : ℝ≥0) (hab : a ≤ b)
    (hfa : Function.leftLim f a = Function.rightLim f a)
    (hflIoc : hg.vectorMeasure.IntegrableOn (Function.leftLim f) (Ioc a b))
    (hflAt : hg.vectorMeasure.IntegrableOn (Function.leftLim f) ({a} : Set ℝ≥0))
    (hgrIoc : hf.vectorMeasure.IntegrableOn (Function.rightLim g) (Ioc a b))
    (hgrAt : hf.vectorMeasure.IntegrableOn (Function.rightLim g) ({a} : Set ℝ≥0))
    (hIoc :
      (∫ᵛ t in Ioc a b, Function.leftLim f t ∂• hg.vectorMeasure) =
        Function.rightLim f b • Function.rightLim g b -
        Function.rightLim f a • Function.rightLim g a -
        (∫ᵛ t in Ioc a b, Function.rightLim g t ∂<• hf.vectorMeasure)) :
    (∫ᵛ t in Icc a b, Function.leftLim f t ∂• hg.vectorMeasure) =
      Function.rightLim f b • Function.rightLim g b -
      Function.leftLim f a • Function.leftLim g a -
      (∫ᵛ t in Icc a b, Function.rightLim g t ∂<• hf.vectorMeasure) := by sorry
