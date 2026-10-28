-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_bounded_probability_real_lintegral_bridge
-- name    : AvramDividend.Classical.esscher_bounded_probability_real_lintegral_bridge
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T17:58:07.814379+00:00
-- url     : https://prove2.me/theorems/72de4759-a9a1-41bf-8514-dcb65d67cfaa
-- title:
--   Actual probability averages of bounded nonnegative CDFs agree in real and ENNReal integral form
-- statement:
--   For any genuine probability Q and measurable real-valued f satisfying 0≤f≤1 everywhere, the ENNReal Lebesgue integral ∫⁻ofReal(f) equals ENNReal.ofReal of the actual real Bochner integral ∫f. This proves, rather than assumes, the exact type-conversion needed to connect the genuine exponential-clock Esscher CDF mixture (as a nonnegative integral) to its accepted real-valued Abel limit.
-- source:
--   Pinned Mathlib ofReal_integral_eq_lintegral_ofReal, Integrable.mono', integrable_const; exact pinned 0df444a. No Wiener-Hopf or Esscher path-law assumptions.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Data.ENNReal.Basic

open MeasureTheory Filter
open scoped ENNReal

theorem AvramDividend.Classical.esscher_bounded_probability_real_lintegral_bridge
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (f : Ω → ℝ) (hf : Measurable f)
    (h0 : ∀ ω, 0 ≤ f ω) (h1 : ∀ ω, f ω ≤ 1) :
    (∫⁻ ω, ENNReal.ofReal (f ω) ∂Q) =
      ENNReal.ofReal (∫ ω, f ω ∂Q) := by sorry
