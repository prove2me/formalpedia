-- Prove2me | Theorems.Thm_ActuarialValuation_jlActualStrain_none
-- name    : ActuarialValuation.jlActualStrain_none
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T19:09:26.511769+00:00
-- url     : https://prove2.me/theorems/c4146d71-221e-4866-8abe-17bda6c53386
-- title:
--   Joint mortality profit and limited-contingent survivor benefits: jlActualStrain_none
-- statement:
--   Both-dead outcome produces its own death strain. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_jlStateStrain
import Definitions.Def_actuarial_jlActualStrain

namespace ActuarialValuation

theorem jlActualStrain_none (pay next : Fin 4 → ℝ) (available : ℝ) : jlActualStrain 3 pay next available=jlStateStrain (pay 3) (next 3) available := by sorry

end ActuarialValuation
