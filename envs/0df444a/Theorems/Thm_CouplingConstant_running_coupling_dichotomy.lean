-- Prove2me | Theorems.Thm_CouplingConstant_running_coupling_dichotomy
-- name    : CouplingConstant.running_coupling_dichotomy
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T21:15:25.697062+00:00
-- url     : https://prove2.me/theorems/fc962d8b-61f9-4692-b7e3-b51b84b47e66
-- title:
--   Running-coupling dichotomy: asymptotic freedom for $b<0$, Landau pole for $b>0$
-- statement:
--   The goal of the mission: the sign of the one-loop coefficient decides, completely, between the two behaviours of a running coupling described in the source.
--
--   Fix a reference scale $t = \log\mu = 0$ and an initial coupling $g_0 > 0$, and let $b$ be the one-loop coefficient, so that the flow equation is $dg/dt = b\,g^{3}$. Then:
--
--   1. **Asymptotic freedom.** If $b < 0$, then *every* $g:\mathbb{R}\to\mathbb{R}$ with $g(0) = g_0$ obeying the flow equation at every $t \ge 0$ satisfies
--   $$\lim_{t\to\infty} g(t) = 0 \qquad\text{and}\qquad \lim_{t\to\infty} 2|b|\,t\,g(t)^{2} = 1,$$
--   so the coupling falls off logarithmically in the energy scale.
--
--   2. **Landau pole.** If $b > 0$, then there is *no* $g:\mathbb{R}\to\mathbb{R}$ with $g(0) = g_0$ obeying the flow equation at every $t$ in the closed interval
--   $$\Big[\,0,\ \tfrac{1}{2\,b\,g_0^{2}}\,\Big];$$
--   the flow cannot be continued to the finite scale $t_\ast = 1/(2bg_0^{2})$.
--
--   The two clauses are exactly the QCD and QED cases discussed in the source, and they are the two sides of the same closed-form solution $g(t)^{-2} = g_0^{-2} - 2bt$: for $b<0$ the right-hand side grows without bound, for $b>0$ it reaches zero at $t_\ast$. The remaining case $b = 0$ is the scale-invariant one and is stated separately among the milestones.
-- source:
--   Wikipedia, "Coupling constant", https://en.wikipedia.org/w/index.php?title=Coupling_constant&oldid=1354339557 — sections "Beta functions", "QED and the Landau pole", "QCD and asymptotic freedom", "QCD scale"

import Mathlib
import Definitions.Def_CouplingConstantDefs

namespace CouplingConstant
theorem running_coupling_dichotomy (b g0 : ℝ) (hg0 : 0 < g0) :
    (b < 0 → ∀ g : ℝ → ℝ, g 0 = g0 → IsOneLoopRunning b g (Set.Ici 0) →
        Filter.Tendsto g Filter.atTop (nhds 0) ∧
          Filter.Tendsto (fun t => (2 * (-b) * t) * (g t) ^ 2) Filter.atTop (nhds 1)) ∧
      (0 < b → ¬ ∃ g : ℝ → ℝ, g 0 = g0 ∧
        IsOneLoopRunning b g (Set.Icc 0 (1 / (2 * b * g0 ^ 2)))) := by sorry
end CouplingConstant
