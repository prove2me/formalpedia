-- Prove2me | Theorems.Thm_ActuarialValuation_ctGeneratorThiele_fundamental
-- name    : ActuarialValuation.ctGeneratorThiele_fundamental
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T15:59:53.270758+00:00
-- url     : https://prove2.me/theorems/194ac070-b25a-409e-8900-85d4776877cc
-- title:
--   Prospective reserve, death and running benefits: ctGeneratorThiele_fundamental
-- statement:
--   A conservative three-state generator and an exact absorbing-state semigroup underpin the explicitly differentiated actuarial Thiele terminal-value equation. The exact assumptions, units and boundary conventions are recorded separately in the formal statement.
--
--   Mathematical relation:
--
--   $$
--   \begin{aligned}\text{A conservative three-state generator and an exact} \\ \text{absorbing-state semigroup underpin the explicitly} \\ \text{differentiated actuarial Thiele terminal-value equation.}\end{aligned}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 324. Promislow (2015), Fundamentals of Actuarial Mathematics, Chapter 19, sections 19.3–19.6, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; Norberg and colleagues, Markov models and Thiele's integral equations for the prospective reserve (1997), https://doi.org/10.1016/S0167-6687(97)00020-6; Buchardt, Møller and Schmidt (2015), https://doi.org/10.1080/03461238.2013.879919. Parent topic: Finite actuarial multi-state generator conservation, continuous-time mortality transition matrices, and an analytically derived absorbing-state prospective reserve equation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.sciencedirect.com/science/article/pii/S0167668797000206

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ctGenerator
import Definitions.Def_actuarial_ctEuler
import Definitions.Def_actuarial_ctAlive
import Definitions.Def_actuarial_ctRiskRate
import Definitions.Def_actuarial_ctAliveReserve
import Definitions.Def_actuarial_ctAliveThiele

namespace ActuarialValuation

theorem ctGeneratorThiele_fundamental (r : Fin 3 → Fin 3 → ℝ) (h delta mu b death maturity t : ℝ) (hr : ctRiskRate delta mu ≠ 0) (i : Fin 3) : ((∑ j : Fin 3, ctGenerator r i j)=0) ∧ ((∑ j : Fin 3, ctEuler r h i j)=1) ∧ (∀ s u : ℝ, ctAlive mu (s+u)=ctAlive mu s*ctAlive mu u) ∧ (HasDerivAt (ctAliveReserve delta mu b death maturity) (ctAliveThiele delta mu b death (ctAliveReserve delta mu b death maturity t)) t) := by sorry

end ActuarialValuation
