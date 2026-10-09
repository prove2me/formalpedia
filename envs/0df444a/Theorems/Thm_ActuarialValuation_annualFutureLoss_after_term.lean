-- Prove2me | Theorems.Thm_ActuarialValuation_annualFutureLoss_after_term
-- name    : ActuarialValuation.annualFutureLoss_after_term
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T23:10:47.557747+00:00
-- url     : https://prove2.me/theorems/384c9ba4-dfee-427f-a63f-afbcafd2a312
-- title:
--   Future loss after maturity
-- statement:
--   No future covered benefits or annual premiums remain once the policy term has expired.
--
--   **Mathematical statement**
--
--   $$
--   t\ge n\Rightarrow L_t=0
--   $$
-- source:
--   Gerber, Life Insurance Mathematics (1997, third edition), Ch.6 §6.3, equations (6.3.4)-(6.3.10); Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2009), Ch.7 §7.3.3, https://doi.org/10.1017/CBO9780511800146.008

import Mathlib
import Definitions.Def_actuarial_annualFutureLoss
open MeasureTheory

namespace ActuarialValuation

theorem annualFutureLoss_after_term {Ω : Type*} (K : Ω → ℕ) (v : ℝ) (n t : ℕ) (b π : ℝ) (ω : Ω) (ht : n ≤ t)
  :
  annualFutureLoss K v n t b π ω = 0 := by sorry

end ActuarialValuation
