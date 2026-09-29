-- Prove2me | Theorems.Thm_CouplingConstant_beta_vanishes_scale_invariant
-- name    : CouplingConstant.beta_vanishes_scale_invariant
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T20:49:24.9334+00:00
-- url     : https://prove2.me/theorems/ffe246fb-1efc-4b71-a3a5-7930826d57ec
-- title:
--   Vanishing beta function: the coupling does not run
-- statement:
--   The source states that if the beta functions of a quantum field theory vanish, the theory is scale invariant. In the one-loop family this is the case $b = 0$.
--
--   Let $g : \mathbb{R}\to\mathbb{R}$ be a coupling as a function of $t = \log\mu$, and suppose it runs at one loop with coefficient $b = 0$ at every scale, i.e.
--   $$\frac{dg}{dt}(t) \;=\; 0\cdot g(t)^{3} \;=\; 0 \qquad \text{for all } t\in\mathbb{R}.$$
--   Then $g$ takes the same value at every scale:
--   $$g(t) \;=\; g(0) \qquad\text{for all } t\in\mathbb{R}.$$
--
--   This is the degenerate end of the dichotomy the mission studies: with no running there is no scale to be singled out, which is exactly the statement that the coupling — and with it the perturbative expansion organised by it — is scale invariant.
-- source:
--   Wikipedia, "Coupling constant", https://en.wikipedia.org/w/index.php?title=Coupling_constant&oldid=1354339557 — sections "Beta functions", "QED and the Landau pole", "QCD and asymptotic freedom", "QCD scale"

import Mathlib
import Definitions.Def_CouplingConstantDefs

namespace CouplingConstant
theorem beta_vanishes_scale_invariant (g : ℝ → ℝ)
    (hg : IsOneLoopRunning 0 g Set.univ) (t : ℝ) :
    g t = g 0 := by sorry
end CouplingConstant
