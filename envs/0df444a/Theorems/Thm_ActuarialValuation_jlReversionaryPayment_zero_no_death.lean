-- Prove2me | Theorems.Thm_ActuarialValuation_jlReversionaryPayment_zero_no_death
-- name    : ActuarialValuation.jlReversionaryPayment_zero_no_death
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T19:11:00.033935+00:00
-- url     : https://prove2.me/theorems/aeac6022-503b-4fc6-b4c4-e0fd1a7c6706
-- title:
--   Joint mortality profit and limited-contingent survivor benefits: jlReversionaryPayment_zero_no_death
-- statement:
--   No member death means no reversionary spouse payment. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
--
--   Mathematical relation:
--
--   $$
--   \Pi_{\text{mort}}=\sum_s p_s D_s-D_{\text{observed}}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 132. Dickson, Hardy and Waters (2020), Actuarial Mathematics for Life Contingent Risks, multiple life insurance and reserves, https://www.cambridge.org/core/books/actuarial-mathematics-for-life-contingent-risks/; S. D. Promislow (2015), Fundamentals of Actuarial Mathematics, multiple-life theory. Parent topic: Independent joint-life outcome probabilities, distinct survivors' reserves, outcome-specific death strain and mortality profit reconciliation with guaranteed reversionary benefits. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.cambridge.org/core/books/actuarial-mathematics-for-life-contingent-risks/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Definitions.Def_actuarial_jlReversionaryPayment

namespace ActuarialValuation

theorem jlReversionaryPayment_zero_no_death (py benefit : ℝ) : jlReversionaryPayment 1 py benefit=0 := by sorry

end ActuarialValuation
