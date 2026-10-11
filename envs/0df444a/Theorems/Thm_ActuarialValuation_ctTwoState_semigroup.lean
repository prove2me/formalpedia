-- Prove2me | Theorems.Thm_ActuarialValuation_ctTwoState_semigroup
-- name    : ActuarialValuation.ctTwoState_semigroup
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T15:56:05.460815+00:00
-- url     : https://prove2.me/theorems/727b65d6-f77e-4c09-bf76-07931271fe0f
-- title:
--   Continuous two-status Markov survival and semigroup: ctTwoState_semigroup
-- statement:
--   Chapman–Kolmogorov holds for every alive/dead transition probability, not only aggregate survival. The exact assumptions, units and boundary conventions are recorded separately in the formal statement.
--
--   Mathematical relation:
--
--   $$
--   \begin{aligned}\text{Chapman–Kolmogorov holds for every alive/dead transition} \\ \text{probability, not only aggregate survival.}\end{aligned}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 324. Promislow (2015), Fundamentals of Actuarial Mathematics, Chapter 19, sections 19.3–19.6, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; Norberg and colleagues, Markov models and Thiele's integral equations for the prospective reserve (1997), https://doi.org/10.1016/S0167-6687(97)00020-6; Buchardt, Møller and Schmidt (2015), https://doi.org/10.1080/03461238.2013.879919. Parent topic: Finite actuarial multi-state generator conservation, continuous-time mortality transition matrices, and an analytically derived absorbing-state prospective reserve equation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.sciencedirect.com/science/article/pii/S0167668797000206

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ctTwoState
import Definitions.Def_actuarial_ctTwoStep

namespace ActuarialValuation

theorem ctTwoState_semigroup (mu s t : ℝ) (i j : Fin 2) : ctTwoState mu (s+t) i j = ctTwoStep (ctTwoState mu s) (ctTwoState mu t) i j := by sorry

end ActuarialValuation
