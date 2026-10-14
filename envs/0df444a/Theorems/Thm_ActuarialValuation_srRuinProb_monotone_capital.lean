-- Prove2me | Theorems.Thm_ActuarialValuation_srRuinProb_monotone_capital
-- name    : ActuarialValuation.srRuinProb_monotone_capital
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T18:17:34.296428+00:00
-- url     : https://prove2.me/theorems/648fd4b5-fad3-45d8-a34a-c86aaa1e2cf3
-- title:
--   Probability of ruin, monotonicity and severity overshoot: srRuinProb_monotone_capital
-- statement:
--   Higher capital cannot increase measured ruin probability. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_srRuinProbability

namespace ActuarialValuation

theorem srRuinProb_monotone_capital {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ] (u v c : ℝ) (W Y : ℕ → Ω → ℝ) (h : u≤v) : srRuinProbability μ v c W Y≤srRuinProbability μ u c W Y := by sorry

end ActuarialValuation
