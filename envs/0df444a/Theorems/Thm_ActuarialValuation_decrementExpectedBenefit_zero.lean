-- Prove2me | Theorems.Thm_ActuarialValuation_decrementExpectedBenefit_zero
-- name    : ActuarialValuation.decrementExpectedBenefit_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-10-08T23:28:02.516692+00:00
-- url     : https://prove2.me/theorems/7f399a19-3dc9-4c72-bd74-53cfff9ab5be
-- title:
--   Zero exit benefits have zero expectation
-- statement:
--   No benefit on any decrement cause makes expected claim outgo zero.
--
--   **Mathematical statement**
--
--   $$
--   B(0)=0
--   $$
-- source:
--   Gerber, Life Insurance Mathematics (1997, third edition), Chapter 7 §7.5, equations (7.5.1)-(7.5.5); Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Chapter 8 §8.8 multiple decrement models, https://doi.org/10.1017/CBO9780511800146.009

import Mathlib
import Definitions.Def_actuarial_decrementExpectedBenefit
open MeasureTheory

namespace ActuarialValuation

theorem decrementExpectedBenefit_zero {J : Type*} [Fintype J] (q : J → ℝ)
  :
  decrementExpectedBenefit q (fun _ => 0) = 0 := by sorry

end ActuarialValuation
