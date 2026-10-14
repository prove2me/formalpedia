-- Prove2me | Theorems.Thm_ActuarialValuation_ctEuler_offdiag
-- name    : ActuarialValuation.ctEuler_offdiag
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T15:50:29.604988+00:00
-- url     : https://prove2.me/theorems/8a3aa18d-5be3-45c6-b3a7-6af51d7b50ee
-- title:
--   Conservative multi-state intensity matrices and forward Euler transition: ctEuler_offdiag
-- statement:
--   Short-time offdiagonal transition weight is step size times intensity. The exact assumptions, units and boundary conventions are recorded separately in the formal statement.
--
--   Mathematical relation:
--
--   $$
--   \begin{aligned}\text{Short-time offdiagonal transition weight is step size times} \\ \text{intensity.}\end{aligned}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 324. Promislow (2015), Fundamentals of Actuarial Mathematics, Chapter 19, sections 19.3–19.6, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; Norberg and colleagues, Markov models and Thiele's integral equations for the prospective reserve (1997), https://doi.org/10.1016/S0167-6687(97)00020-6; Buchardt, Møller and Schmidt (2015), https://doi.org/10.1080/03461238.2013.879919. Parent topic: Finite actuarial multi-state generator conservation, continuous-time mortality transition matrices, and an analytically derived absorbing-state prospective reserve equation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.sciencedirect.com/science/article/pii/S0167668797000206

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ctEuler

namespace ActuarialValuation

theorem ctEuler_offdiag (r : Fin 3 → Fin 3 → ℝ) (h : ℝ) (i j : Fin 3) (hij : i ≠ j) : ctEuler r h i j = h*r i j := by sorry

end ActuarialValuation
