-- Prove2me | Theorems.Thm_ActuarialValuation_srRuinDeficit_at_ruin
-- name    : ActuarialValuation.srRuinDeficit_at_ruin
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T18:10:30.093993+00:00
-- url     : https://prove2.me/theorems/2f6252bd-e976-4872-b1a7-a93c6278e54d
-- title:
--   Probability of ruin, monotonicity and severity overshoot: srRuinDeficit_at_ruin
-- statement:
--   At insolvency the deficit equals negative surplus. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
--
--   Mathematical relation:
--
--   $$
--   \psi_N(u)=\mathbb{P}(\min_{n\le N}U_n<0)
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 3. S. David Promislow (2015), Fundamentals of Actuarial Mathematics, chapter 23, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; Hanspeter Schmidli, Risk Theory (2017), https://link.springer.com/book/10.1007/978-3-319-72005-0; probability ruin bound overview https://www.mdpi.com/2227-9091/12/2/28. Parent topic: Actual compound-Poisson embedded arrival paths, measurable first ruin events, disjoint first-hit times, deficit and conditional stopped-exponential Lundberg bound. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.mdpi.com/2227-9091/12/2/28

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_srSurplus
import Definitions.Def_actuarial_srRuinAt
import Definitions.Def_actuarial_srRuinDeficit

namespace ActuarialValuation

theorem srRuinDeficit_at_ruin {Ω : Type*} (u c : ℝ) (W Y : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (h : srRuinAt u c W Y n ω) : srRuinDeficit u c W Y n ω= -srSurplus u c W Y n ω := by sorry

end ActuarialValuation
