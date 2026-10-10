-- Prove2me | Theorems.Thm_ActuarialValuation_annualDecrementLaw_cause_nonnegative
-- name    : ActuarialValuation.annualDecrementLaw_cause_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T23:24:21.885997+00:00
-- url     : https://prove2.me/theorems/d3f72358-afca-48cd-aab3-a5ba5e842210
-- title:
--   Each cause probability is nonnegative
-- statement:
--   Every cause probability is a nonnegative entry of the decrement law.
--
--   **Mathematical statement**
--
--   $$
--   q_j\ge0
--   $$
-- source:
--   Gerber, Life Insurance Mathematics (1997, third edition), Chapter 7 §7.5, equations (7.5.1)-(7.5.5); Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Chapter 8 §8.8 multiple decrement models, https://doi.org/10.1017/CBO9780511800146.009

import Mathlib
import Definitions.Def_actuarial_isAnnualDecrementLaw
open MeasureTheory

namespace ActuarialValuation

theorem annualDecrementLaw_cause_nonnegative {J : Type*} [Fintype J] (p : ℝ) (q : J → ℝ)
  (h : isAnnualDecrementLaw p q) (j : J)
  :
  0 ≤ q j := by sorry

end ActuarialValuation
