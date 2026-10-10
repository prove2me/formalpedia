-- Prove2me | Theorems.Thm_CosmologyEOS_dust_energy_density_scaling
-- name    : CosmologyEOS.dust_energy_density_scaling
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:33:24.285977+00:00
-- url     : https://prove2.me/theorems/e9961bf7-5977-4974-8914-e23330b1a9b9
-- title:
--   Non-relativistic matter: $\varepsilon \propto a^{-3}$
-- statement:
--   Let $I\subseteq\mathbb R$ be an open, connected set of times and let $a,\varepsilon,p$ be real functions of time such that on $I$: $a$ and $\varepsilon$ are differentiable, $a>0$, the equation of state is $p = 0\,\varepsilon$, and the fluid equation $\dot\varepsilon = -3\frac{\dot a}{a}(\varepsilon + p)$ holds. Then for all $s,t\in I$
--
--   $$\varepsilon(t)\,a(t)^{3} = \varepsilon(s)\,a(s)^{3},$$
--
--   i.e. $\varepsilon \propto a^{-3}$.
--
--   This is the non-relativistic matter case of the general scaling law $\varepsilon\propto a^{-3(1+w)}$.
-- source:
--   Wikipedia, "Equation of state (cosmology)", revision 1375011367, https://en.wikipedia.org/w/index.php?title=Equation_of_state_(cosmology)&oldid=1375011367, section 'Non-relativistic particles'

import Mathlib
import Definitions.Def_CosmologyEOS_Defs

open Real Filter Topology

namespace CosmologyEOS

theorem dust_energy_density_scaling (a ε p : ℝ → ℝ) (I : Set ℝ)
    (hI_open : IsOpen I) (hI_conn : IsPreconnected I)
    (ha_diff : ∀ t ∈ I, DifferentiableAt ℝ a t)
    (hε_diff : ∀ t ∈ I, DifferentiableAt ℝ ε t)
    (ha_pos : ∀ t ∈ I, 0 < a t)
    (heos : ∀ t ∈ I, p t = 0 * ε t)
    (hfluid : ∀ t ∈ I, FluidEquation a ε p t) :
    ∀ s ∈ I, ∀ t ∈ I, ε t * a t ^ 3 = ε s * a s ^ 3 := by
  sorry

end CosmologyEOS
