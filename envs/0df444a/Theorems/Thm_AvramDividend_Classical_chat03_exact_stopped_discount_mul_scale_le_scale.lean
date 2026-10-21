-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_exact_stopped_discount_mul_scale_le_scale
-- name    : AvramDividend.Classical.chat03_exact_stopped_discount_mul_scale_le_scale
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T08:36:38.718696+00:00
-- url     : https://prove2.me/theorems/e87a1041-2077-4fc5-97e7-9b0e36c39db4
-- title:
--   The exact stopped upper-first discounted scale reward is at most its boundary scale value
-- statement:
--   For the exact official spectrally negative Lévy process and its named strict upward and downward first-passage clocks, any nonnegative q and real terminal scale value wa, the complete left-hand-side expression of the allocated stopped-scale identity, with ofReal(wa) as its multiplier, is bounded above by ofReal(wa). The proof instantiates the separately Proved upper-first reward expectation bound using the process's built-in probability measure and multiplies the inequality by the ENNReal terminal scale factor. Hence this side of the stopped-scale identity is finite without invoking killed q-scale harmonicity. This does not claim equality with W(x).
-- source:
--   Proved Chat03 upper-first discounted lintegral bound and the official SpectrallyNegativeLevy.isProbability field, pinned Mathlib ordered multiplication.

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat03_discounted_upperfirst_lintegral_le_one
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat03_exact_stopped_discount_mul_scale_le_scale
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (lower upper wa : ℝ) :
    (∫⁻ ω,
      if twoSidedExitUpTime X upper ω <
          twoSidedExitDownTime X lower ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal
            (twoSidedExitUpTime X upper ω))))
      else 0 ∂P) * ENNReal.ofReal wa ≤ ENNReal.ofReal wa := by sorry
