-- Prove2me | Theorems.Thm_ActuarialValuation_jlOutcomeSum_one
-- name    : ActuarialValuation.jlOutcomeSum_one
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T19:03:18.613916+00:00
-- url     : https://prove2.me/theorems/29f09921-3ecf-4e42-baee-542173c94982
-- title:
--   Independent joint-life outcomes and probabilities: jlOutcomeSum_one
-- statement:
--   Four alive/dead combinations exhaust a two-life year. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
--
--   Mathematical relation:
--
--   $$
--   p_{xy}=p_xp_y,\quad p_{x\dagger y}=(1-p_x)p_y
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 132. Dickson, Hardy and Waters (2020), Actuarial Mathematics for Life Contingent Risks, multiple life insurance and reserves, https://www.cambridge.org/core/books/actuarial-mathematics-for-life-contingent-risks/; S. D. Promislow (2015), Fundamentals of Actuarial Mathematics, multiple-life theory. Parent topic: Independent joint-life outcome probabilities, distinct survivors' reserves, outcome-specific death strain and mortality profit reconciliation with guaranteed reversionary benefits. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.cambridge.org/core/books/actuarial-mathematics-for-life-contingent-risks/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Definitions.Def_actuarial_jlBothAlive
import Definitions.Def_actuarial_jlOnlyXAlive
import Definitions.Def_actuarial_jlOnlyYAlive
import Definitions.Def_actuarial_jlBothDead

namespace ActuarialValuation

theorem jlOutcomeSum_one (px py : ℝ) : jlBothAlive px py+jlOnlyXAlive px py+jlOnlyYAlive px py+jlBothDead px py=1 := by sorry

end ActuarialValuation
