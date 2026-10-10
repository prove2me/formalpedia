-- Prove2me | Theorems.Thm_ActuarialValuation_pvPortfolioMean_empty
-- name    : ActuarialValuation.pvPortfolioMean_empty
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:20:33.027756+00:00
-- url     : https://prove2.me/theorems/5c417732-53cf-4052-b804-889fe596a8e7
-- title:
--   Equivalence premiums and loss variance: pvPortfolioMean_empty
-- statement:
--   An empty policy portfolio has zero aggregate expected loss.
--
--   Mathematical relation:
--
--   $$
--   pvPortfolioMean\_empty
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 15 and 16, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/globalassets/assets/files/edu/fall2006webcatalog.pdf. Published source page 235 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvPortfolioMean

namespace ActuarialValuation

theorem pvPortfolioMean_empty (means : ℕ → ℝ) : pvPortfolioMean means 0 = 0 := by sorry

end ActuarialValuation
