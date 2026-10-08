-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_eq_q_of_ae_zero_origin_C2
-- name    : AvramDividend.Classical.scaleFunction_generator_eq_q_of_ae_zero_origin_C2
-- status  : Open
-- author  : @WillR
-- created : 2026-10-08T13:06:22.522508+00:00
-- url     : https://prove2.me/theorems/f649867a-7a17-4b6a-94b6-202d2e322f82
-- title:
--   Pointwise q-harmonicity for zero-origin C2 scale functions from a.e. harmonicity
-- statement:
--   When W(0)=0 and W is C2 on (0,a), continuity of W at all shifted jump arguments and a quadratic Lévy envelope imply continuity of ΓW-qW on (0,a). A Lebesgue-a.e. harmonic generator equation then upgrades to the pointwise identity throughout that interval. This theorem keeps the a.e. generator identity as an explicit input; it does not silently assume it from compact Fubini or the scale-function Laplace transform.
-- source:
--   Local generator residual continuity and a.e.-to-pointwise q-harmonicity bridge, Avram Dividend Lemma 4.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_generator_eq_q_of_ae_zero_origin_C2
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hzero : W 0 = 0)
    (a : ℝ) (ha : 0 < a)
    (hC2 : ContDiffOn ℝ 2 W (Ioo 0 a))
    (hae : ∀ᵐ x ∂(volume.restrict (Ioo 0 a)),
      X.generator W x - q * W x = 0) :
    ∀ x ∈ Ioo 0 a, X.generator W x - q * W x = 0 := by sorry

end AvramDividend.Classical
