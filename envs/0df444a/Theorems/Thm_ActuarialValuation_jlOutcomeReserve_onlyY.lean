-- Prove2me | Theorems.Thm_ActuarialValuation_jlOutcomeReserve_onlyY
-- name    : ActuarialValuation.jlOutcomeReserve_onlyY
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T19:05:50.802754+00:00
-- url     : https://prove2.me/theorems/7eb56173-556d-49e7-9603-2542b30d50b0
-- title:
--   Outcome-dependent reserves, benefits and death strain: jlOutcomeReserve_onlyY
-- statement:
--   Only the second surviving life retains its single-life reserve. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_jlOutcomeReserve

namespace ActuarialValuation

theorem jlOutcomeReserve_onlyY (a b c d : ℝ) : jlOutcomeReserve a b c d 2=c := by sorry

end ActuarialValuation
