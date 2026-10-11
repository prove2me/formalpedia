-- Prove2me | Theorems.Thm_ActuarialValuation_srFirstHit_is_ruin
-- name    : ActuarialValuation.srFirstHit_is_ruin
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T18:08:03.875751+00:00
-- url     : https://prove2.me/theorems/fead336a-5dd0-4610-a130-3a8ba020ccdd
-- title:
--   Embedded Poisson-arrival capital paths and first-passage partition: srFirstHit_is_ruin
-- statement:
--   First failure implies failure at the claimed time. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_srRuinAt
import Definitions.Def_actuarial_srFirstHit

namespace ActuarialValuation

theorem srFirstHit_is_ruin {Ω : Type*} (u c : ℝ) (W Y : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : srFirstHit u c W Y n ω → srRuinAt u c W Y n ω := by sorry

end ActuarialValuation
