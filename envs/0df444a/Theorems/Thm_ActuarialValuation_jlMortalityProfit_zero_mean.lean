-- Prove2me | Theorems.Thm_ActuarialValuation_jlMortalityProfit_zero_mean
-- name    : ActuarialValuation.jlMortalityProfit_zero_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T19:10:17.311586+00:00
-- url     : https://prove2.me/theorems/d1fdd39c-66a5-4ad9-92aa-1f20bfc878ad
-- title:
--   Joint mortality profit and limited-contingent survivor benefits: jlMortalityProfit_zero_mean
-- statement:
--   Under the genuine normalized four-outcome distribution, mortality experience profit has expectation zero. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_jlProbability
import Definitions.Def_actuarial_jlMortalityProfit

namespace ActuarialValuation

theorem jlMortalityProfit_zero_mean (px py : ℝ) (pay next : Fin 4 → ℝ) (available : ℝ) : (∑ s : Fin 4, jlProbability px py s*jlMortalityProfit px py pay next available s)=0 := by sorry

end ActuarialValuation
