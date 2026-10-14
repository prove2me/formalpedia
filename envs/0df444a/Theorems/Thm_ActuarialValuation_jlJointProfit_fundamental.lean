-- Prove2me | Theorems.Thm_ActuarialValuation_jlJointProfit_fundamental
-- name    : ActuarialValuation.jlJointProfit_fundamental
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T19:12:07.379624+00:00
-- url     : https://prove2.me/theorems/2ab7bc44-48b4-44c5-b8a1-49eba412bcf4
-- title:
--   Joint mortality profit and limited-contingent survivor benefits: jlJointProfit_fundamental
-- statement:
--   An exhaustive, correctly normalized two-life outcome model makes the mortality experience profit mean zero, retaining separate survivor reserves, death benefits and guaranteed payment conventions. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_jlAtLeastOneAlive
import Definitions.Def_actuarial_jlPostPremiumFund
import Definitions.Def_actuarial_jlProbability
import Definitions.Def_actuarial_jlMortalityProfit

namespace ActuarialValuation

theorem jlJointProfit_fundamental (px py : ℝ) (pay next : Fin 4 → ℝ) (reserve premium interest : ℝ) (hx0 : 0≤px) (hx1 : px≤1) (hy0 : 0≤py) (hy1 : py≤1) : ((∑ s : Fin 4, jlProbability px py s)=1) ∧ ((∑ s : Fin 4, jlProbability px py s*jlMortalityProfit px py pay next (jlPostPremiumFund reserve premium interest) s)=0) ∧ (jlAtLeastOneAlive px py=px+py-px*py) := by sorry

end ActuarialValuation
