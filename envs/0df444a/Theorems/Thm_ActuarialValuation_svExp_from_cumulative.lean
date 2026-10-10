-- Prove2me | Theorems.Thm_ActuarialValuation_svExp_from_cumulative
-- name    : ActuarialValuation.svExp_from_cumulative
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:23:22.474995+00:00
-- url     : https://prove2.me/theorems/be459e04-2952-4c52-b01b-c077cae2dda2
-- title:
--   Exponential Gompertz Makeham hazards and insurance valuation: svExp_from_cumulative
-- statement:
--   For a constant hazard the cumulative force reconstructs the same exponential survival factor.
--
--   Mathematical relation:
--
--   $$
--   svExp\_from\_cumulative
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 14, 8 and Appendix A, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.actuaries.org.uk/system/files/field/document/Technical%20Workshop%20October%202019%20Slide%20Deck.pdf. Published source page 211 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_actuarial_svSurvivalFromCumulativeHazard
import Definitions.Def_actuarial_svExpCumulativeHazard
import Definitions.Def_actuarial_svExpSurvival

namespace ActuarialValuation

theorem svExp_from_cumulative (lambda t : ℝ) : svSurvivalFromCumulativeHazard (svExpCumulativeHazard lambda t) = svExpSurvival lambda t := by sorry

end ActuarialValuation
