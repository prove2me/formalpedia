-- Prove2me | Theorems.Thm_ActuarialValuation_decrementExpectedBenefit_scale
-- name    : ActuarialValuation.decrementExpectedBenefit_scale
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T23:29:00.229548+00:00
-- url     : https://prove2.me/theorems/59121d99-5c03-4560-8f15-0503718de669
-- title:
--   Cause-specific benefit valuation is linear in sums assured
-- statement:
--   Scaling all cause-specific benefits scales the weighted outgo by the same amount.
--
--   **Mathematical statement**
--
--   $$
--   B(ab)=aB(b)
--   $$
-- source:
--   Gerber, Life Insurance Mathematics (1997, third edition), Chapter 7 §7.5, equations (7.5.1)-(7.5.5); Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Chapter 8 §8.8 multiple decrement models, https://doi.org/10.1017/CBO9780511800146.009

import Mathlib
import Definitions.Def_actuarial_decrementExpectedBenefit
open MeasureTheory

namespace ActuarialValuation

theorem decrementExpectedBenefit_scale {J : Type*} [Fintype J] (q b : J → ℝ) (a : ℝ)
  :
  decrementExpectedBenefit q (fun j => a * b j) = a * decrementExpectedBenefit q b := by sorry

end ActuarialValuation
