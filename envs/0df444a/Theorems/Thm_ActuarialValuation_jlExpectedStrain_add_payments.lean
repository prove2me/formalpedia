-- Prove2me | Theorems.Thm_ActuarialValuation_jlExpectedStrain_add_payments
-- name    : ActuarialValuation.jlExpectedStrain_add_payments
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T19:08:12.772382+00:00
-- url     : https://prove2.me/theorems/f27afa98-9487-4115-a944-0761016b7451
-- title:
--   Outcome-dependent reserves, benefits and death strain: jlExpectedStrain_add_payments
-- statement:
--   Additional state-specific benefit claims add to expected death strain. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_jlProbability
import Definitions.Def_actuarial_jlExpectedStrain

namespace ActuarialValuation

theorem jlExpectedStrain_add_payments (px py : ℝ) (benefit extra reserve : Fin 4 → ℝ) (available : ℝ) : jlExpectedStrain px py (fun s => benefit s+extra s) reserve available=jlExpectedStrain px py benefit reserve available+(∑ s : Fin 4, jlProbability px py s*extra s) := by sorry

end ActuarialValuation
