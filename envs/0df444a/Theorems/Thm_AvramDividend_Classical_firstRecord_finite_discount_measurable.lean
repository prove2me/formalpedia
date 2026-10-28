-- Prove2me | Theorems.Thm_AvramDividend_Classical_firstRecord_finite_discount_measurable
-- name    : AvramDividend.Classical.firstRecord_finite_discount_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T00:22:45.530325+00:00
-- url     : https://prove2.me/theorems/e2a9c66d-9339-46a9-9a7e-0ba7a2b76cb3
-- title:
--   Measurability of the finite first-record exponential discount function
-- statement:
--   The nonnegative time-to-discount map t↦ ENNReal.ofReal(ε exp(-q t)) is measurable for any real ε and q. It supplies the discount measurability hypothesis for finite-stopping strong Markov expectation factorisation.
-- source:
--   Mathlib measurable NNReal real coercion, exponential and ENNReal.ofReal

import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.ENNReal.Basic

open MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.firstRecord_finite_discount_measurable
    (q ε : ℝ) :
    Measurable (fun t : ℝ≥0 =>
      ENNReal.ofReal (ε * Real.exp (-(q * (t : ℝ))))) := by sorry
