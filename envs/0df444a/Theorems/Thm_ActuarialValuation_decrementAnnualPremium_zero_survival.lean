-- Prove2me | Theorems.Thm_ActuarialValuation_decrementAnnualPremium_zero_survival
-- name    : ActuarialValuation.decrementAnnualPremium_zero_survival
-- status  : Open
-- author  : @WillR
-- created : 2026-10-08T23:32:05.717125+00:00
-- url     : https://prove2.me/theorems/133f793b-f5ef-42fc-87f9-8bb3aa111a62
-- title:
--   Annual premium when no policy survives
-- statement:
--   When the in-force policy must exit in the year, there is no next-year survival reserve term.
--
--   **Mathematical statement**
--
--   $$
--   p=0\Rightarrow\Pi=vB-R
--   $$
-- source:
--   Gerber, Life Insurance Mathematics (1997, third edition), Chapter 7 §7.5, equations (7.5.1)-(7.5.5); Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Chapter 8 §8.8 multiple decrement models, https://doi.org/10.1017/CBO9780511800146.009

import Mathlib
import Definitions.Def_actuarial_decrementAnnualPremium
import Definitions.Def_actuarial_decrementExpectedBenefit
open MeasureTheory

namespace ActuarialValuation

theorem decrementAnnualPremium_zero_survival {J : Type*} [Fintype J] (p : ℝ) (q b : J → ℝ) (v R Rnext : ℝ) (hp : p = 0)
  :
  decrementAnnualPremium p q b v R Rnext =
    v * decrementExpectedBenefit q b - R := by sorry

end ActuarialValuation
