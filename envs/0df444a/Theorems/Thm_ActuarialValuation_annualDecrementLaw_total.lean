-- Prove2me | Theorems.Thm_ActuarialValuation_annualDecrementLaw_total
-- name    : ActuarialValuation.annualDecrementLaw_total
-- status  : Open
-- author  : @WillR
-- created : 2026-10-08T23:27:16.252808+00:00
-- url     : https://prove2.me/theorems/a22fa445-7d6f-4441-a643-d2b1860294d5
-- title:
--   Survival and all decrement causes total one
-- statement:
--   All mutually exclusive annual outcomes exhaust total conditional probability.
--
--   **Mathematical statement**
--
--   $$
--   p+\sum_jq_j=1
--   $$
-- source:
--   Gerber, Life Insurance Mathematics (1997, third edition), Chapter 7 §7.5, equations (7.5.1)-(7.5.5); Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Chapter 8 §8.8 multiple decrement models, https://doi.org/10.1017/CBO9780511800146.009

import Mathlib
import Definitions.Def_actuarial_isAnnualDecrementLaw
open MeasureTheory

namespace ActuarialValuation

theorem annualDecrementLaw_total {J : Type*} [Fintype J] (p : ℝ) (q : J → ℝ)
  (h : isAnnualDecrementLaw p q)
  :
  p + (∑ j : J, q j) = 1 := by sorry

end ActuarialValuation
