-- Prove2me | Theorems.Thm_CosmologyEOS_cosmological_constant_exponential_expansion
-- name    : CosmologyEOS.cosmological_constant_exponential_expansion
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:35:44.816923+00:00
-- url     : https://prove2.me/theorems/a25c4f4a-8d48-45ef-b51a-e93b5a27efa3
-- title:
--   Cosmological constant $w=-1$: $a \propto e^{Ht}$
-- statement:
--   Let $G>0$ and let $a,\varepsilon,p$ be real functions of time, differentiable everywhere, with $a>0$, equation of state $p = -\varepsilon$ (i.e. $w=-1$), satisfying the fluid equation $\dot\varepsilon = -3\frac{\dot a}{a}(\varepsilon+p)$ and the flat Friedmann equation $\left(\frac{\dot a}{a}\right)^2 = \frac{8\pi G}{3}\varepsilon$ at all times. Then the energy density is constant and the scale factor is exponential: there are constants $H$ and $C>0$ with
--
--   $$H^2 = \frac{8\pi G}{3}\,\varepsilon(0),\qquad a(t) = C\,e^{Ht},\qquad \varepsilon(t) = \varepsilon(0)\quad\text{for all } t\in\mathbb R.$$
--
--   Here $H$ is the Hubble parameter.
--
--   **Formalization Note** $H$ is allowed to have either sign (an expanding or contracting de Sitter solution); the source's expanding case is $H>0$.
-- source:
--   Wikipedia, "Equation of state (cosmology)", revision 1375011367, https://en.wikipedia.org/w/index.php?title=Equation_of_state_(cosmology)&oldid=1375011367, section 'Acceleration of cosmic inflation' (w = −1, a ∝ e^{Ht})

import Mathlib
import Definitions.Def_CosmologyEOS_Defs

open Real Filter Topology

namespace CosmologyEOS

theorem cosmological_constant_exponential_expansion (G : ℝ) (hG : 0 < G) (a ε p : ℝ → ℝ)
    (ha_diff : ∀ t, DifferentiableAt ℝ a t)
    (hε_diff : ∀ t, DifferentiableAt ℝ ε t)
    (ha_pos : ∀ t, 0 < a t)
    (heos : ∀ t, p t = -1 * ε t)
    (hfluid : ∀ t, FluidEquation a ε p t)
    (hfried : ∀ t, FlatFriedmannEquation G a ε t) :
    ∃ H C : ℝ, 0 < C ∧ H ^ 2 = 8 * π * G / 3 * ε 0 ∧
      ∀ t, a t = C * Real.exp (H * t) ∧ ε t = ε 0 := by
  sorry

end CosmologyEOS
