-- Prove2me | Theorems.Thm_CosmologyEOS_energy_density_scaling
-- name    : CosmologyEOS.energy_density_scaling
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:31:18.584679+00:00
-- url     : https://prove2.me/theorems/e0429920-b1e0-4dee-8c10-76fd2b2ba617
-- title:
--   Energy density scales as $a^{-3(1+w)}$
-- statement:
--   Let $I\subseteq\mathbb R$ be an open, connected set of times and let $w\in\mathbb R$. Let $a,\varepsilon,p$ be real functions of time such that on $I$: $a$ and $\varepsilon$ are differentiable, $a>0$, the fluid has constant equation of state $p = w\varepsilon$, and the fluid equation $\dot\varepsilon = -3\frac{\dot a}{a}(\varepsilon + p)$ holds. Then for all $s,t\in I$
--
--   $$\varepsilon(t)\,a(t)^{3(1+w)} = \varepsilon(s)\,a(s)^{3(1+w)},$$
--
--   i.e. $\varepsilon \propto a^{-3(1+w)}$.
--
--   This is the basic dilution law of a perfect fluid in an FLRW universe; every special case in the source (dust, radiation, stiff matter, cosmological constant) is an instance.
--
--   **Formalization Note** The power $a^{3(1+w)}$ is a real power (`Real.rpow`) of the positive number $a$. No sign condition on $\varepsilon$ is assumed.
-- source:
--   Wikipedia, "Equation of state (cosmology)", revision 1375011367, https://en.wikipedia.org/w/index.php?title=Equation_of_state_(cosmology)&oldid=1375011367, section 'FLRW equations and the equation of state' (ε ∝ a^{-3(1+w)})

import Mathlib
import Definitions.Def_CosmologyEOS_Defs

open Real Filter Topology

namespace CosmologyEOS

theorem energy_density_scaling (w : ℝ) (a ε p : ℝ → ℝ) (I : Set ℝ)
    (hI_open : IsOpen I) (hI_conn : IsPreconnected I)
    (ha_diff : ∀ t ∈ I, DifferentiableAt ℝ a t)
    (hε_diff : ∀ t ∈ I, DifferentiableAt ℝ ε t)
    (ha_pos : ∀ t ∈ I, 0 < a t)
    (heos : ∀ t ∈ I, p t = w * ε t)
    (hfluid : ∀ t ∈ I, FluidEquation a ε p t) :
    ∀ s ∈ I, ∀ t ∈ I,
      ε t * a t ^ (3 * (1 + w)) = ε s * a s ^ (3 * (1 + w)) := by
  sorry

end CosmologyEOS
