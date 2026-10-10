-- Prove2me | Theorems.Thm_CosmologyEOS_flat_universe_power_law
-- name    : CosmologyEOS.flat_universe_power_law
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:32:11.637684+00:00
-- url     : https://prove2.me/theorems/f9c4b50b-36a0-4a73-a7e5-1d43f5e1e554
-- title:
--   Flat universe dominated by one fluid: $a \propto t^{2/(3(1+w))}$
-- statement:
--   Let $G>0$ be Newton's constant and let $w>-1$. Let $a,\varepsilon,p$ be real functions of time such that for every $t>0$: $a$ and $\varepsilon$ are differentiable at $t$, $a(t)>0$, $p(t) = w\,\varepsilon(t)$, the fluid equation $\dot\varepsilon = -3\frac{\dot a}{a}(\varepsilon+p)$ holds, and the flat Friedmann equation $\left(\frac{\dot a}{a}\right)^2 = \frac{8\pi G}{3}\varepsilon$ holds. Suppose the universe starts from a big bang at $t = 0$, i.e. $a(t)\to 0$ as $t\to 0^+$. Then there is a constant $C>0$ such that
--
--   $$a(t) = C\,t^{\frac{2}{3(1+w)}}\qquad\text{for all } t>0.$$
--
--   This is the source's statement that, if the fluid is the dominant form of matter in a flat universe, $a\propto t^{2/(3(1+w))}$, where $t$ is the proper time.
--
--   **Formalization Note** The proportionality is normalized by placing the big bang at $t=0$. Neither monotonicity of $a$ nor positivity of $\varepsilon$ is assumed; the hypothesis $w>-1$ is where the source's exponent is defined (the case $w=-1$ is treated separately).
-- source:
--   Wikipedia, "Equation of state (cosmology)", revision 1375011367, https://en.wikipedia.org/w/index.php?title=Equation_of_state_(cosmology)&oldid=1375011367, section 'FLRW equations and the equation of state' (a ∝ t^{2/(3(1+w))})

import Mathlib
import Definitions.Def_CosmologyEOS_Defs

open Real Filter Topology

namespace CosmologyEOS

theorem flat_universe_power_law (G w : ℝ) (hG : 0 < G) (hw : -1 < w) (a ε p : ℝ → ℝ)
    (ha_diff : ∀ t > 0, DifferentiableAt ℝ a t)
    (hε_diff : ∀ t > 0, DifferentiableAt ℝ ε t)
    (ha_pos : ∀ t > 0, 0 < a t)
    (heos : ∀ t > 0, p t = w * ε t)
    (hfluid : ∀ t > 0, FluidEquation a ε p t)
    (hfried : ∀ t > 0, FlatFriedmannEquation G a ε t)
    (hbang : Tendsto a (𝓝[>] 0) (𝓝 0)) :
    ∃ C > 0, ∀ t > 0, a t = C * t ^ (2 / (3 * (1 + w))) := by
  sorry

end CosmologyEOS
