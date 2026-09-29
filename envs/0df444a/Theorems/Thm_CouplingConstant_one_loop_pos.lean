-- Prove2me | Theorems.Thm_CouplingConstant_one_loop_pos
-- name    : CouplingConstant.one_loop_pos
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T20:54:07.697016+00:00
-- url     : https://prove2.me/theorems/e63e6309-3c57-4bd5-9651-3bb2d9000094
-- title:
--   A one-loop coupling started positive stays positive
-- statement:
--   A coupling that solves the one-loop flow equation and is positive at the reference scale remains positive as long as the flow is defined.
--
--   Let $b$ be a real one-loop coefficient, let $T \ge 0$, and let $g:\mathbb{R}\to\mathbb{R}$ satisfy
--   $$\frac{dg}{dt}(t) = b\,g(t)^{3}\qquad\text{for every } t\in[0,T],\qquad g(0) = g_0 > 0 .$$
--   Then
--   $$g(t) > 0 \qquad \text{for every } t \in [0,T].$$
--
--   The statement is the technical prerequisite of the exact solution: the one-loop equation is solved by differentiating $t\mapsto g(t)^{-2}$, which is only legitimate where $g$ does not vanish. It holds for either sign of $b$ and for every interval on which the flow is assumed, so it is also what makes the Landau-pole argument possible.
-- source:
--   Wikipedia, "Coupling constant", https://en.wikipedia.org/w/index.php?title=Coupling_constant&oldid=1354339557 — sections "Beta functions", "QED and the Landau pole", "QCD and asymptotic freedom", "QCD scale"

import Mathlib
import Definitions.Def_CouplingConstantDefs

namespace CouplingConstant
theorem one_loop_pos (b g0 T : ℝ) (g : ℝ → ℝ) (hg0 : 0 < g0) (h0 : g 0 = g0)
    (hT : 0 ≤ T) (hg : IsOneLoopRunning b g (Set.Icc 0 T)) :
    ∀ t ∈ Set.Icc 0 T, 0 < g t := by sorry
end CouplingConstant
