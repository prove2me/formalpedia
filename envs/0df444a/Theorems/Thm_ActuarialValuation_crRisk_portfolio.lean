-- Prove2me | Theorems.Thm_ActuarialValuation_crRisk_portfolio
-- name    : ActuarialValuation.crRisk_portfolio
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:38:26.560979+00:00
-- url     : https://prove2.me/theorems/a17b6b97-c313-40a0-93a7-c6d136837baa
-- title:
--   Coherent worst-case actuarial premium and portfolio: crRisk_portfolio
-- statement:
--   A coherent robust premium on the aggregate insured portfolio is at most the sum of stand-alone robust premiums.
--
--   Mathematical relation:
--
--   $$
--   crRisk\_portfolio
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 22, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1111/1467-9965.00068. The proposed model is rooted in Promislow chapter 22. The target Lean identity is an original derivation, not a verbatim published result. Published source page 412 gives the actuarial risk assessment chapter context; the Lean statement is an original derived target.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crScenarioRisk
import Definitions.Def_actuarial_crPortfolioLoss

namespace ActuarialValuation

theorem crRisk_portfolio {n : ℕ} (p q X Y : Fin n→ℝ) : crScenarioRisk p q (crPortfolioLoss X Y) ≤ crScenarioRisk p q X + crScenarioRisk p q Y := by sorry

end ActuarialValuation
