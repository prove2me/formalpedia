-- Prove2me | Theorems.Thm_ActuarialValuation_ctAliveReserve_terminal
-- name    : ActuarialValuation.ctAliveReserve_terminal
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T15:57:52.642933+00:00
-- url     : https://prove2.me/theorems/6fa47bce-1948-401e-8f6b-6807a694d01c
-- title:
--   Prospective reserve, death and running benefits: ctAliveReserve_terminal
-- statement:
--   A terminal-zero finite-term reserve has no liability at contract expiry. The exact assumptions, units and boundary conventions are recorded separately in the formal statement.
--
--   Mathematical relation:
--
--   $$
--   \begin{aligned}\text{A terminal-zero finite-term reserve has no liability at} \\ \text{contract expiry.}\end{aligned}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 324. Promislow (2015), Fundamentals of Actuarial Mathematics, Chapter 19, sections 19.3–19.6, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; Norberg and colleagues, Markov models and Thiele's integral equations for the prospective reserve (1997), https://doi.org/10.1016/S0167-6687(97)00020-6; Buchardt, Møller and Schmidt (2015), https://doi.org/10.1080/03461238.2013.879919. Parent topic: Finite actuarial multi-state generator conservation, continuous-time mortality transition matrices, and an analytically derived absorbing-state prospective reserve equation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.sciencedirect.com/science/article/pii/S0167668797000206

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ctRiskRate
import Definitions.Def_actuarial_ctAliveReserve

namespace ActuarialValuation

theorem ctAliveReserve_terminal (delta mu b death maturity : ℝ) (h : ctRiskRate delta mu ≠ 0) : ctAliveReserve delta mu b death maturity maturity = 0 := by sorry

end ActuarialValuation
