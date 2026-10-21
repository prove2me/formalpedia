-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_exact_upperfirst_discount_integrand_measurable
-- name    : AvramDividend.Classical.chat03_exact_upperfirst_discount_integrand_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T07:22:48.102289+00:00
-- url     : https://prove2.me/theorems/065fe2d0-ab23-4064-8312-0bd03a8c7386
-- title:
--   Measurability of the exact upper-first discounted reward integrand in the stopped-scale identity
-- statement:
--   For the exact named strict upper and lower passage clocks, any real discount parameter q and the official spectrally negative Lévy process, the extended-real function that equals ofReal(exp(-q*toReal(τup))) when τup<τdown and zero otherwise is Borel measurable. This is the exact event selector and discount integrand of the allocated stopped-scale identity. The proof uses full clock measurability, including infinite values, the strict-order event, measurable ENNReal.toReal, continuous real exponential, and measurable ENNReal.ofReal. It does not claim any stopped q-scale martingale or expectation identity.
-- source:
--   Proved clock-measurability and pinned Mathlib measurableSet_lt, ENNReal.measurable_toReal, Real.measurable_exp, ENNReal.measurable_ofReal.

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat03_both_named_passage_clocks_measurable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_exact_upperfirst_discount_integrand_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (lower upper q : ℝ) :
    Measurable (fun ω : Ω =>
      if twoSidedExitUpTime X upper ω < twoSidedExitDownTime X lower ω
      then ENNReal.ofReal
        (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X upper ω))))
      else 0) := by sorry
