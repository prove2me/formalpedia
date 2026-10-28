-- Prove2me | Theorems.Thm_AvramDividend_Classical_capped_record_exponential_discount_measurable
-- name    : AvramDividend.Classical.capped_record_exponential_discount_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T09:33:27.977749+00:00
-- url     : https://prove2.me/theorems/5584be31-b23c-4e74-a514-e82ae56ac3a4
-- title:
--   Measurability of the nonnegative exponential record-discount weight
-- statement:
--   For all real dividend sizes ε and discount parameters q, the nonnegative extended-real weight ε-positive-part times exp(-q t) is measurable in nonnegative time t. This discharges the stopped-Markov discount measurability condition for the first-record renewal lower bound.
-- source:
--   Standard Mathlib measurability of real exponential, scalar multiplication, coercion of NNReal time to Real, and ofReal into ENNReal.

import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic.FunProp

open MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.capped_record_exponential_discount_measurable (ε q : ℝ) :
    Measurable (fun t : ℝ≥0 =>
      ENNReal.ofReal ε * ENNReal.ofReal (Real.exp (-(q * (t : ℝ))))) := by sorry
