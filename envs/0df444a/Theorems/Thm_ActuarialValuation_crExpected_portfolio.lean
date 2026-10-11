-- Prove2me | Theorems.Thm_ActuarialValuation_crExpected_portfolio
-- name    : ActuarialValuation.crExpected_portfolio
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:34:20.187634+00:00
-- url     : https://prove2.me/theorems/3315ea84-4f98-4402-8f25-3e488c99156f
-- title:
--   Actual finite loss distributions and scenario ambiguity: crExpected_portfolio
-- statement:
--   Actual portfolio-sum expected loss reconciles to individual expected claims despite shared dependence.
--
--   Mathematical relation:
--
--   $$
--   crExpected\_portfolio
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 22, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1111/1467-9965.00068. The proposed model is rooted in Promislow chapter 22. The target Lean identity is an original derivation, not a verbatim published result. Published source page 412 gives the actuarial risk assessment chapter context; the Lean statement is an original derived target.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crExpected
import Definitions.Def_actuarial_crPortfolioLoss

namespace ActuarialValuation

theorem crExpected_portfolio {n : ℕ} (p X Y : Fin n→ℝ) : crExpected p (crPortfolioLoss X Y) = crExpected p X+crExpected p Y := by sorry

end ActuarialValuation
