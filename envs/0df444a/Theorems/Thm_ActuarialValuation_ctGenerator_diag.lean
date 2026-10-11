-- Prove2me | Theorems.Thm_ActuarialValuation_ctGenerator_diag
-- name    : ActuarialValuation.ctGenerator_diag
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T15:48:21.902709+00:00
-- url     : https://prove2.me/theorems/46d0aec8-4a86-4f18-ab63-3de73ad3d1bb
-- title:
--   Conservative multi-state intensity matrices and forward Euler transition: ctGenerator_diag
-- statement:
--   The generator diagonal is the negative sum of outgoing nonself intensities. The exact assumptions, units and boundary conventions are recorded separately in the formal statement.
--
--   Mathematical relation:
--
--   $$
--   \begin{aligned}\text{The generator diagonal is the negative sum of outgoing nonself} \\ \text{intensities.}\end{aligned}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 324. Promislow (2015), Fundamentals of Actuarial Mathematics, Chapter 19, sections 19.3–19.6, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; Norberg and colleagues, Markov models and Thiele's integral equations for the prospective reserve (1997), https://doi.org/10.1016/S0167-6687(97)00020-6; Buchardt, Møller and Schmidt (2015), https://doi.org/10.1080/03461238.2013.879919. Parent topic: Finite actuarial multi-state generator conservation, continuous-time mortality transition matrices, and an analytically derived absorbing-state prospective reserve equation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.sciencedirect.com/science/article/pii/S0167668797000206

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ctRateOut
import Definitions.Def_actuarial_ctGenerator

namespace ActuarialValuation

theorem ctGenerator_diag (r : Fin 3 → Fin 3 → ℝ) (i : Fin 3) : ctGenerator r i i = -ctRateOut r i := by sorry

end ActuarialValuation
