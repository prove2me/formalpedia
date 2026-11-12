-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_charfun_product_measure_fubini_20261111
-- name    : AvramDividend.Classical.avram_a06_charfun_product_measure_fubini_20261111
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T20:37:21.036431+00:00
-- url     : https://prove2.me/theorems/a28b85cd-2614-4a4d-a98c-779aff8ef9af
-- title:
--   Characteristic function of measurable product-measure image disintegrates over the first factor
-- statement:
--   General one-dimensional characteristic-function Fubini: for any real measurable observable of a product probability law, its characteristic function is the integral of conditional characteristic functions over the first factor. Obtain by expressing charFun with the complex unit-modulus exponential, proving integrability and applying Mathlib integral_prod. This is independent of the particular Lévy or A06 setting.

import Mathlib
open MeasureTheory ProbabilityTheory
noncomputable section

theorem AvramDividend.Classical.avram_a06_charfun_product_measure_fubini_20261111
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : A × B → ℝ) (hf : Measurable f) (t : ℝ) :
    MeasureTheory.charFun (Measure.map f (μ.prod ν)) t =
      ∫ a, MeasureTheory.charFun (Measure.map (fun b => f (a,b)) ν) t ∂μ := by sorry
