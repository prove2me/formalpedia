-- Prove2me | Theorems.Thm_ActuarialValuation_annualDecrementLaw_survival_nonnegative
-- name    : ActuarialValuation.annualDecrementLaw_survival_nonnegative
-- status  : Open
-- author  : @WillR
-- created : 2026-10-08T23:23:03.932004+00:00
-- url     : https://prove2.me/theorems/04ea62fb-4845-4cb6-8ca7-90207055b97a
-- title:
--   Survival probability is nonnegative
-- statement:
--   The annual decrement law explicitly requires nonnegative survival mass.
--
--   **Mathematical statement**
--
--   $$
--   p\ge0
--   $$
-- source:
--   Gerber, Life Insurance Mathematics (1997, third edition), Chapter 7 §7.5, equations (7.5.1)-(7.5.5); Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Chapter 8 §8.8 multiple decrement models, https://doi.org/10.1017/CBO9780511800146.009

import Mathlib
import Definitions.Def_actuarial_isAnnualDecrementLaw
open MeasureTheory

namespace ActuarialValuation

theorem annualDecrementLaw_survival_nonnegative {J : Type*} [Fintype J] (p : ℝ) (q : J → ℝ)
  (h : isAnnualDecrementLaw p q)
  :
  0 ≤ p := by sorry

end ActuarialValuation
