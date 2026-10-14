-- Prove2me | Theorems.Thm_ActuarialValuation_crRisk_cash
-- name    : ActuarialValuation.crRisk_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:35:54.6893+00:00
-- url     : https://prove2.me/theorems/b72798ae-c92d-49a7-ad35-3dc95704267a
-- title:
--   Coherent worst-case actuarial premium and portfolio: crRisk_cash
-- statement:
--   Robust insurer capital is translation invariant for certain additional monetary losses under normalised candidate laws.
--
--   Mathematical relation:
--
--   $$
--   crRisk\_cash
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 22, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1111/1467-9965.00068. The proposed model is rooted in Promislow chapter 22. The target Lean identity is an original derivation, not a verbatim published result. Published source page 412 gives the actuarial risk assessment chapter context; the Lean statement is an original derived target.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crScenarioRisk

namespace ActuarialValuation

theorem crRisk_cash {n : ℕ} (p q X : Fin n→ℝ) (c : ℝ) (hp : (∑ i : Fin n,p i)=1) (hq : (∑ i : Fin n,q i)=1) : crScenarioRisk p q (fun i=>X i+c) = crScenarioRisk p q X+c := by sorry

end ActuarialValuation
