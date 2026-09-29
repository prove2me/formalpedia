-- Prove2me | Theorems.Thm_CouplingConstant_landau_pole
-- name    : CouplingConstant.landau_pole
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T21:14:05.073793+00:00
-- url     : https://prove2.me/theorems/723388a3-d125-4121-8afe-c5f7b8bfd6c3
-- title:
--   Landau pole: for $b>0$ the flow does not reach $t_\ast=1/(2bg_0^2)$
-- statement:
--   This is the Landau-pole statement: a positive one-loop coefficient makes the coupling blow up at a finite energy scale, so no solution of the flow equation survives up to that scale.
--
--   Let $b > 0$ and $g_0 > 0$, and set
--   $$t_\ast \;=\; \frac{1}{2\,b\,g_0^{2}} \;>\;0 .$$
--   Then there is **no** function $g:\mathbb{R}\to\mathbb{R}$ with
--   $$g(0) = g_0 \qquad\text{and}\qquad \frac{dg}{dt}(t) = b\,g(t)^{3}\ \text{ for every } t\in[0,t_\ast].$$
--
--   Equivalently, the one-loop flow started at $g_0$ cannot be continued to the scale $\log\mu = t_\ast$: by the closed-form solution $g(t)^{-2} = g_0^{-2} - 2bt$, the right-hand side reaches $0$ exactly at $t_\ast$. This is the Landau pole of the perturbative one-loop approximation, the phenomenon the source records for QED, where the beta function is positive and the coupling "apparently becomes infinite at some finite energy". The statement is about the one-loop flow only, and makes no claim about the true high-energy behaviour of the theory.
-- source:
--   Wikipedia, "Coupling constant", https://en.wikipedia.org/w/index.php?title=Coupling_constant&oldid=1354339557 — sections "Beta functions", "QED and the Landau pole", "QCD and asymptotic freedom", "QCD scale"

import Mathlib
import Definitions.Def_CouplingConstantDefs

namespace CouplingConstant
theorem landau_pole (b g0 : ℝ) (hb : 0 < b) (hg0 : 0 < g0) :
    ¬ ∃ g : ℝ → ℝ, g 0 = g0 ∧
      IsOneLoopRunning b g (Set.Icc 0 (1 / (2 * b * g0 ^ 2))) := by sorry
end CouplingConstant
