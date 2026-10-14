-- Prove2me | Theorems.Thm_ActuarialValuation_jlStateStrain_balance
-- name    : ActuarialValuation.jlStateStrain_balance
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T19:07:32.692313+00:00
-- url     : https://prove2.me/theorems/912f6c05-b48a-496b-9ac7-5b0a2ee4812c
-- title:
--   Outcome-dependent reserves, benefits and death strain: jlStateStrain_balance
-- statement:
--   Future obligations and immediate benefits reconcile the observed death strain. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
--
--   Mathematical relation:
--
--   $$
--   D_{s}=B_s+V_s-(V_0+P)(1+i)
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 132. Dickson, Hardy and Waters (2020), Actuarial Mathematics for Life Contingent Risks, multiple life insurance and reserves, https://www.cambridge.org/core/books/actuarial-mathematics-for-life-contingent-risks/; S. D. Promislow (2015), Fundamentals of Actuarial Mathematics, multiple-life theory. Parent topic: Independent joint-life outcome probabilities, distinct survivors' reserves, outcome-specific death strain and mortality profit reconciliation with guaranteed reversionary benefits. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.cambridge.org/core/books/actuarial-mathematics-for-life-contingent-risks/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Definitions.Def_actuarial_jlStateStrain

namespace ActuarialValuation

theorem jlStateStrain_balance (benefit next available : ℝ) : jlStateStrain benefit next available+available=benefit+next := by sorry

end ActuarialValuation
