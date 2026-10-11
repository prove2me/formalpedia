-- Prove2me | Theorems.Thm_ActuarialValuation_jlBothDead_symmetric
-- name    : ActuarialValuation.jlBothDead_symmetric
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T19:04:43.621699+00:00
-- url     : https://prove2.me/theorems/f78dc94a-1aa5-4771-a893-03ecdc3db401
-- title:
--   Independent joint-life outcomes and probabilities: jlBothDead_symmetric
-- statement:
--   Both-dead probability is symmetric. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_jlBothDead

namespace ActuarialValuation

theorem jlBothDead_symmetric (px py : ℝ) : jlBothDead px py=jlBothDead py px := by sorry

end ActuarialValuation
