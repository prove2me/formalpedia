-- Prove2me | Theorems.Thm_ActuarialValuation_ctAliveThiele_linear
-- name    : ActuarialValuation.ctAliveThiele_linear
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T15:59:24.656625+00:00
-- url     : https://prove2.me/theorems/e678b07f-09c0-4f07-b357-985fb0d0c03f
-- title:
--   Prospective reserve, death and running benefits: ctAliveThiele_linear
-- statement:
--   Increasing the reserve shifts the derivative by force-of-risk times additional liability. The exact assumptions, units and boundary conventions are recorded separately in the formal statement.
--
--   Mathematical relation:
--
--   $$
--   \begin{aligned}\text{Increasing the reserve shifts the derivative by force-of-risk} \\ \text{times additional liability.}\end{aligned}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 324. Promislow (2015), Fundamentals of Actuarial Mathematics, Chapter 19, sections 19.3–19.6, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; Norberg and colleagues, Markov models and Thiele's integral equations for the prospective reserve (1997), https://doi.org/10.1016/S0167-6687(97)00020-6; Buchardt, Møller and Schmidt (2015), https://doi.org/10.1080/03461238.2013.879919. Parent topic: Finite actuarial multi-state generator conservation, continuous-time mortality transition matrices, and an analytically derived absorbing-state prospective reserve equation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.sciencedirect.com/science/article/pii/S0167668797000206

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ctRiskRate
import Definitions.Def_actuarial_ctAliveThiele

namespace ActuarialValuation

theorem ctAliveThiele_linear (delta mu b death v w : ℝ) : ctAliveThiele delta mu b death (v+w) = ctAliveThiele delta mu b death v + ctRiskRate delta mu*w := by sorry

end ActuarialValuation
