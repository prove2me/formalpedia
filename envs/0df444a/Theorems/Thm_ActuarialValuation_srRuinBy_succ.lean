-- Prove2me | Theorems.Thm_ActuarialValuation_srRuinBy_succ
-- name    : ActuarialValuation.srRuinBy_succ
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T18:07:05.911387+00:00
-- url     : https://prove2.me/theorems/cc586d76-fb90-450a-8e3b-24a96291a8cb
-- title:
--   Embedded Poisson-arrival capital paths and first-passage partition: srRuinBy_succ
-- statement:
--   Once a path has failed it is counted as failed at later horizons. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
--
--   Mathematical relation:
--
--   $$
--   U_n=u+c\sum_{j<n}W_j-\sum_{j<n}Y_j
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 3. S. David Promislow (2015), Fundamentals of Actuarial Mathematics, chapter 23, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; Hanspeter Schmidli, Risk Theory (2017), https://link.springer.com/book/10.1007/978-3-319-72005-0; probability ruin bound overview https://www.mdpi.com/2227-9091/12/2/28. Parent topic: Actual compound-Poisson embedded arrival paths, measurable first ruin events, disjoint first-hit times, deficit and conditional stopped-exponential Lundberg bound. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.mdpi.com/2227-9091/12/2/28

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_srRuinBy

namespace ActuarialValuation

theorem srRuinBy_succ {Ω : Type*} (u c : ℝ) (W Y : ℕ → Ω → ℝ) (N : ℕ) (ω : Ω) : srRuinBy u c W Y N ω → srRuinBy u c W Y (N+1) ω := by sorry

end ActuarialValuation
