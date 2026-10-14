-- Prove2me | Theorems.Thm_ActuarialValuation_jlGuaranteedPayment_after
-- name    : ActuarialValuation.jlGuaranteedPayment_after
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T19:11:50.311924+00:00
-- url     : https://prove2.me/theorems/59f61433-d532-4de6-a976-56cb34f5bd42
-- title:
--   Joint mortality profit and limited-contingent survivor benefits: jlGuaranteedPayment_after
-- statement:
--   After guarantee expiry, payment is conditional on life survival. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_jlGuaranteedPayment

namespace ActuarialValuation

theorem jlGuaranteedPayment_after (survival benefit : ℝ) : jlGuaranteedPayment survival benefit 0=survival*benefit := by sorry

end ActuarialValuation
