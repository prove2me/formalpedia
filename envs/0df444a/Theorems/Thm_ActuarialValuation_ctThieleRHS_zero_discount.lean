-- Prove2me | Theorems.Thm_ActuarialValuation_ctThieleRHS_zero_discount
-- name    : ActuarialValuation.ctThieleRHS_zero_discount
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T15:52:49.125999+00:00
-- url     : https://prove2.me/theorems/0d01e3ab-256e-48e7-ae42-055126376dac
-- title:
--   Conservative multi-state intensity matrices and forward Euler transition: ctThieleRHS_zero_discount
-- statement:
--   At zero force of interest only payment and transition effects remain. The exact assumptions, units and boundary conventions are recorded separately in the formal statement.
--
--   Mathematical relation:
--
--   $$
--   \begin{aligned}\text{At zero force of interest only payment and transition effects} \\ \text{remain.}\end{aligned}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 324. Promislow (2015), Fundamentals of Actuarial Mathematics, Chapter 19, sections 19.3–19.6, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; Norberg and colleagues, Markov models and Thiele's integral equations for the prospective reserve (1997), https://doi.org/10.1016/S0167-6687(97)00020-6; Buchardt, Møller and Schmidt (2015), https://doi.org/10.1080/03461238.2013.879919. Parent topic: Finite actuarial multi-state generator conservation, continuous-time mortality transition matrices, and an analytically derived absorbing-state prospective reserve equation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.sciencedirect.com/science/article/pii/S0167668797000206

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ctBackward
import Definitions.Def_actuarial_ctThieleRHS

namespace ActuarialValuation

theorem ctThieleRHS_zero_discount (q : Fin 3 → Fin 3 → ℝ) (b v : Fin 3 → ℝ) (i : Fin 3) : ctThieleRHS q 0 b v i = -b i-ctBackward q v i := by sorry

end ActuarialValuation
