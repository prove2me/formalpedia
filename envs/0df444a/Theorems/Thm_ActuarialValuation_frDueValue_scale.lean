-- Prove2me | Theorems.Thm_ActuarialValuation_frDueValue_scale
-- name    : ActuarialValuation.frDueValue_scale
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:22:21.512224+00:00
-- url     : https://prove2.me/theorems/deca92d9-95d3-409d-9556-9649b5a9679e
-- title:
--   Frequency-dependent annuity cashflow valuation: frDueValue_scale
-- statement:
--   Subannual valuation is homogeneous in the monetary benefit schedule for a fixed valuation basis.
--
--   Mathematical relation:
--
--   $$
--   frDueValue\_scale
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 7, 4 and 8, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/498941/globalassets/assets/files/e-business/pd/events/2018/las/pd-2018-05-las-session-033.pdf. Published source page 98 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_frDueValue

namespace ActuarialValuation

theorem frDueValue_scale (c : ℕ → ℝ) (discount : ℝ → ℝ) (p q : ℕ → ℝ) (n m : ℕ) (a : ℝ) : frDueValue (fun k => a*c k) discount p q n m = a * frDueValue c discount p q n m := by sorry

end ActuarialValuation
