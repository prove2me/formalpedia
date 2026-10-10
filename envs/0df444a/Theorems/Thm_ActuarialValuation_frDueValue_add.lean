-- Prove2me | Theorems.Thm_ActuarialValuation_frDueValue_add
-- name    : ActuarialValuation.frDueValue_add
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:22:42.274689+00:00
-- url     : https://prove2.me/theorems/4b33c08f-9790-43eb-bb1b-41b592a35d11
-- title:
--   Frequency-dependent annuity cashflow valuation: frDueValue_add
-- statement:
--   Subannual annuity values add across simultaneous benefit streams with the same survival and discount basis.
--
--   Mathematical relation:
--
--   $$
--   frDueValue\_add
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 7, 4 and 8, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/498941/globalassets/assets/files/e-business/pd/events/2018/las/pd-2018-05-las-session-033.pdf. Published source page 98 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_frDueValue

namespace ActuarialValuation

theorem frDueValue_add (a b : ℕ → ℝ) (discount : ℝ → ℝ) (p q : ℕ → ℝ) (n m : ℕ) : frDueValue (fun k => a k+b k) discount p q n m = frDueValue a discount p q n m + frDueValue b discount p q n m := by sorry

end ActuarialValuation
