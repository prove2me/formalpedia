-- Prove2me | Theorems.Thm_ActuarialValuation_srExpLoss_at_ruin
-- name    : ActuarialValuation.srExpLoss_at_ruin
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T18:22:38.78799+00:00
-- url     : https://prove2.me/theorems/23c3d59e-caa5-4b52-a5e5-82f93f80cc0c
-- title:
--   Stopped exponential-loss process and conditional Lundberg capital bound: srExpLoss_at_ruin
-- statement:
--   At first passage exponential net losses exceed the capital threshold. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
--
--   Mathematical relation:
--
--   $$
--   \mathbb{E}[M_{\tau\wedge N}]\le1\ \Longrightarrow\ \psi_N(u)\le e^{-Ru}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 3. S. David Promislow (2015), Fundamentals of Actuarial Mathematics, chapter 23, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; Hanspeter Schmidli, Risk Theory (2017), https://link.springer.com/book/10.1007/978-3-319-72005-0; probability ruin bound overview https://www.mdpi.com/2227-9091/12/2/28. Parent topic: Actual compound-Poisson embedded arrival paths, measurable first ruin events, disjoint first-hit times, deficit and conditional stopped-exponential Lundberg bound. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.mdpi.com/2227-9091/12/2/28

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_srRuinAt
import Definitions.Def_actuarial_srExpLoss

namespace ActuarialValuation

theorem srExpLoss_at_ruin {Ω : Type*} (R u c : ℝ) (W Y : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (hR : 0<R) (h : srRuinAt u c W Y n ω) : Real.exp (R*u)<srExpLoss R c W Y n ω := by sorry

end ActuarialValuation
