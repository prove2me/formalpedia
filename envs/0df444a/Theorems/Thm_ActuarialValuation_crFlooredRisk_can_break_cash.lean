-- Prove2me | Theorems.Thm_ActuarialValuation_crFlooredRisk_can_break_cash
-- name    : ActuarialValuation.crFlooredRisk_can_break_cash
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:42:03.308565+00:00
-- url     : https://prove2.me/theorems/9d478ce4-99e4-4080-bdf4-c22be2aed255
-- title:
--   Stop-loss risk comparison and limitations of floored risk principles: crFlooredRisk_can_break_cash
-- statement:
--   Concrete counterexample underlying failure of translation invariance for a nonnegative floor: adding one to a certain loss of minus one does not increase floored capital.
--
--   Mathematical relation:
--
--   $$
--   crFlooredRisk\_can\_break\_cash
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 22, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1111/1467-9965.00068. The proposed model is rooted in Promislow chapter 22. The target Lean identity is an original derivation, not a verbatim published result. Published source page 412 gives the actuarial risk assessment chapter context; the Lean statement is an original derived target.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crFlooredRisk

namespace ActuarialValuation

theorem crFlooredRisk_can_break_cash (p q : Fin 2→ℝ) (hp : (∑ i : Fin 2,p i)=1) (hq : (∑ i : Fin 2,q i)=1) : crFlooredRisk p q (fun _=>-1)=0 ∧ crFlooredRisk p q (fun _=>0)=0 := by sorry

end ActuarialValuation
