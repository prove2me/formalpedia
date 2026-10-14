-- Prove2me | Theorems.Thm_ActuarialValuation_ruSurplus_issue
-- name    : ActuarialValuation.ruSurplus_issue
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:35:41.940406+00:00
-- url     : https://prove2.me/theorems/792f592d-06ad-4964-b7d0-2af1415b0dec
-- title:
--   Actuarial surplus and exponential supermartingale: ruSurplus_issue
-- statement:
--   At issue, insurer surplus equals its initial capital before any realised net cashflow.
--
--   Mathematical relation:
--
--   $$
--   ruSurplus\_issue
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 18 and 23, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://ocw.mit.edu/courses/18-440-probability-and-random-variables-spring-2014/resources/mit18_440s14_lecture35/. The proposed model is rooted in Promislow chapter 18 and 23. The target Lean identity is an original derivation, not a verbatim published result. Published source page 426 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_ruSurplus

namespace ActuarialValuation

theorem ruSurplus_issue {m : ℕ} (u : ℝ) (G : ℕ → Fin m → ℝ) (ω : Fin m) : ruSurplus u G 0 ω = u := by sorry

end ActuarialValuation
