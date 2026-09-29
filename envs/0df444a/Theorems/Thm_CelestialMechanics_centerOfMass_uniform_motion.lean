-- Prove2me | Theorems.Thm_CelestialMechanics_centerOfMass_uniform_motion
-- name    : CelestialMechanics.centerOfMass_uniform_motion
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T18:22:20.225517+00:00
-- url     : https://prove2.me/theorems/de574f53-fa43-4f1d-b63d-a84b74eba816
-- title:
--   The center of mass of a binary system moves with constant velocity
-- statement:
--   **The center of mass frame is inertial.** Because the gravitational forces the two stars exert on each other are equal and opposite, $m_1\ddot{\mathbf{r}}_1+m_2\ddot{\mathbf{r}}_2=0$, so the center of mass
--
--   $$ \mathbf{R}(t) = \frac{m_1\mathbf{r}_1(t)+m_2\mathbf{r}_2(t)}{m_1+m_2} $$
--
--   has vanishing acceleration and therefore moves in a straight line at constant velocity: there are a fixed point $\mathbf{R}_0$ and a fixed vector $\mathbf{V}$ with $\mathbf{R}(t)=\mathbf{R}_0+t\,\mathbf{V}$ for all $t$. This is what licenses Fitzpatrick's passage to the *center of mass frame* preceding Eqs. (4.118)-(4.119).
-- source:
--   Richard Fitzpatrick, *Celestial Mechanics* (University of Texas at Austin, lecture notes), Chapter 4 "Keplerian orbits", Section 4.16 "Binary star systems", https://farside.ph.utexas.edu/teaching/celestial/Celestial/node38.html, Eqs. (4.108)-(4.119)

import Mathlib
import Definitions.Def_CelestialMechanics_binary_star_dynamics

namespace CelestialMechanics
theorem centerOfMass_uniform_motion (G m₁ m₂ : ℝ) (r₁ r₂ : ℝ → Space)
    (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (h : IsNewtonianTwoBody G m₁ m₂ r₁ r₂) :
    ∃ R₀ V : Space, ∀ t, centerOfMass m₁ m₂ r₁ r₂ t = R₀ + t • V := by sorry
end CelestialMechanics
