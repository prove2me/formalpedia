-- Prove2me | Theorems.Thm_ActuarialValuation_jlMortalityProfit_difference
-- name    : ActuarialValuation.jlMortalityProfit_difference
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T19:10:36.195202+00:00
-- url     : https://prove2.me/theorems/3c2618bd-1f54-400f-9a8f-fd2b4ff09cf0
-- title:
--   Joint mortality profit and limited-contingent survivor benefits: jlMortalityProfit_difference
-- statement:
--   Expected and actual mortality strain reconcile exactly to profit. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_jlExpectedStrain
import Definitions.Def_actuarial_jlActualStrain
import Definitions.Def_actuarial_jlMortalityProfit

namespace ActuarialValuation

theorem jlMortalityProfit_difference (px py : ℝ) (pay next : Fin 4 → ℝ) (available : ℝ) (s : Fin 4) : jlMortalityProfit px py pay next available s+jlActualStrain s pay next available=jlExpectedStrain px py pay next available := by sorry

end ActuarialValuation
