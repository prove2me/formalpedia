-- Prove2me | Theorems.Thm_ActuarialValuation_erRuin_candidate_fundamental
-- name    : ActuarialValuation.erRuin_candidate_fundamental
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T16:03:31.957012+00:00
-- url     : https://prove2.me/theorems/e4f60681-9b6d-4a8e-8440-38cea9cf34a4
-- title:
--   Explicit ruin candidate and exact renewal valuation: erRuin_candidate_fundamental
-- statement:
--   The nontrivial adjustment coefficient controls the exact exponential candidate, whose derivative and true renewal integral satisfy the classical ruin integro-differential equation. The exact assumptions, units and boundary conventions are recorded separately in the formal statement.
--
--   Mathematical relation:
--
--   $$
--   \begin{aligned}\text{The nontrivial adjustment coefficient controls the exact} \\ \text{exponential candidate, whose derivative and true renewal} \\ \text{integral satisfy the classical ruin integro-differential} \\ \text{equation.}\end{aligned}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 438. S. David Promislow (2015), Fundamentals of Actuarial Mathematics, Chapter 23, sections 23.3–23.7; Hanspeter Schmidli, Risk Theory (2017), Springer Actuarial, https://link.springer.com/book/10.1007/978-3-319-72005-0; Palmowski et al. 2020, https://doi.org/10.1007/s13385-020-00223-4. Parent topic: Compound Poisson surplus with exponentially distributed claims, net profit, adjustment root, exact candidate ruin function and renewal differential/integral equation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_erAdjustment
import Definitions.Def_actuarial_erLundbergGap
import Definitions.Def_actuarial_erNetLossMGF
import Definitions.Def_actuarial_erRuinCandidate
import Definitions.Def_actuarial_erRuinDerivativeRHS
import Definitions.Def_actuarial_erRuinEquationResidual

namespace ActuarialValuation

theorem erRuin_candidate_fundamental (lambda c beta u : ℝ) (hl : 0<lambda) (hc : 0<c) (hb : 0<beta) (hn : lambda<c*beta) (hu : 0≤u) : (0<erAdjustment lambda c beta) ∧ (erLundbergGap lambda c beta (erAdjustment lambda c beta)=0) ∧ (erNetLossMGF lambda c beta (erAdjustment lambda c beta) u=1) ∧ (HasDerivAt (erRuinCandidate lambda c beta) (erRuinDerivativeRHS lambda c beta u) u) ∧ (erRuinEquationResidual lambda c beta u=0) := by sorry

end ActuarialValuation
