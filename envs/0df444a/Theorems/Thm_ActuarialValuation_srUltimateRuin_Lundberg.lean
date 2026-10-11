-- Prove2me | Theorems.Thm_ActuarialValuation_srUltimateRuin_Lundberg
-- name    : ActuarialValuation.srUltimateRuin_Lundberg
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T18:24:55.550977+00:00
-- url     : https://prove2.me/theorems/ef3348a5-ee9f-4cb9-b096-01c9a8ea1252
-- title:
--   Stopped exponential-loss process and conditional Lundberg capital bound: srUltimateRuin_Lundberg
-- statement:
--   Finite-horizon stopped exponential bounds imply an ultimate ruin probability bound by monotone convergence. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_srRuinProbability
import Definitions.Def_actuarial_srLundbergBound
import Definitions.Def_actuarial_srStoppedExp
import Definitions.Def_actuarial_srStoppedMoment

namespace ActuarialValuation

theorem srUltimateRuin_Lundberg {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ] (R u c : ℝ) (W Y : ℕ → Ω → ℝ) (hR : 0<R) (hW : ∀ j, Measurable (W j)) (hY : ∀ j, Measurable (Y j)) (hint : ∀ N : ℕ, MeasureTheory.Integrable (srStoppedExp R u c W Y N) μ) (hstop : ∀ N, srStoppedMoment μ R u c W Y N≤1) : srRuinProbability μ u c W Y≤srLundbergBound R u := by sorry

end ActuarialValuation
