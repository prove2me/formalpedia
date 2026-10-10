-- Prove2me | Theorems.Thm_ActuarialValuation_frDueTerm_zero
-- name    : ActuarialValuation.frDueTerm_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:19:48.929983+00:00
-- url     : https://prove2.me/theorems/d6a15cf7-870c-4874-9cce-7638615a97a7
-- title:
--   Frequency-dependent annuity cashflow valuation: frDueTerm_zero
-- statement:
--   A zero scheduled subannual due cashflow contributes zero present value.
--
--   Mathematical relation:
--
--   $$
--   frDueTerm\_zero
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 7, 4 and 8, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/498941/globalassets/assets/files/e-business/pd/events/2018/las/pd-2018-05-las-session-033.pdf. Published source page 98 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_frDueTerm

namespace ActuarialValuation

theorem frDueTerm_zero (c : ℕ → ℝ) (discount : ℝ → ℝ) (p q : ℕ → ℝ) (k j m : ℕ) (h : c k = 0) : frDueTerm c discount p q k j m = 0 := by sorry

end ActuarialValuation
