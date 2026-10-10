-- Prove2me | Theorems.Thm_ActuarialValuation_svExp_start
-- name    : ActuarialValuation.svExp_start
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:22:33.758979+00:00
-- url     : https://prove2.me/theorems/5e287876-0c59-41ab-b463-913cf49e339e
-- title:
--   Exponential Gompertz Makeham hazards and insurance valuation: svExp_start
-- statement:
--   Exponential lifetime model has unit survivor function at duration zero.
--
--   Mathematical relation:
--
--   $$
--   svExp\_start
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 14, 8 and Appendix A, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.actuaries.org.uk/system/files/field/document/Technical%20Workshop%20October%202019%20Slide%20Deck.pdf. Published source page 211 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_actuarial_svExpSurvival

namespace ActuarialValuation

theorem svExp_start (lambda : ℝ) : svExpSurvival lambda 0 = 1 := by sorry

end ActuarialValuation
