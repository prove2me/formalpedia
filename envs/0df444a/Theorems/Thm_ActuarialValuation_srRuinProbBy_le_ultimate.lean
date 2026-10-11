-- Prove2me | Theorems.Thm_ActuarialValuation_srRuinProbBy_le_ultimate
-- name    : ActuarialValuation.srRuinProbBy_le_ultimate
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T18:18:28.410039+00:00
-- url     : https://prove2.me/theorems/99734377-6294-4493-a3eb-45055363c093
-- title:
--   Probability of ruin, monotonicity and severity overshoot: srRuinProbBy_le_ultimate
-- statement:
--   Ruin through finitely many claims is contained in ultimate ruin. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_srRuinProbabilityBy

namespace ActuarialValuation

theorem srRuinProbBy_le_ultimate {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ] (u c : ℝ) (W Y : ℕ → Ω → ℝ) (N : ℕ) : srRuinProbabilityBy μ u c W Y N≤srRuinProbability μ u c W Y := by sorry

end ActuarialValuation
