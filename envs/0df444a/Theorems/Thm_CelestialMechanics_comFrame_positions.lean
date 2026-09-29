-- Prove2me | Theorems.Thm_CelestialMechanics_comFrame_positions
-- name    : CelestialMechanics.comFrame_positions
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T18:22:54.023219+00:00
-- url     : https://prove2.me/theorems/bac61337-2ba0-477b-90f5-934d0296a13f
-- title:
--   Eqs. (4.118)-(4.119): $\mathbf{r}_1 = -\frac{m_2}{m_1+m_2}\mathbf{r}$, $\mathbf{r}_2 = \frac{m_1}{m_1+m_2}\mathbf{r}$
-- statement:
--   **Equations (4.118)-(4.119).** Work in the inertial frame whose origin is the common center of mass, i.e. assume $m_1\mathbf{r}_1(t)+m_2\mathbf{r}_2(t)=\mathbf{0}$ at all times. Then the individual positions of the two stars are determined by the relative separation $\mathbf{r}=\mathbf{r}_2-\mathbf{r}_1$:
--
--   $$ \mathbf{r}_1 = -\frac{m_2}{m_1+m_2}\,\mathbf{r}, \qquad \mathbf{r}_2 = \frac{m_1}{m_1+m_2}\,\mathbf{r}. $$
--
--   In particular each star traces a scaled copy of the relative orbit, and at every instant the two stars lie diametrically opposite one another with respect to the origin. This is pure kinematics: no dynamical assumption is used.
-- source:
--   Richard Fitzpatrick, *Celestial Mechanics* (University of Texas at Austin, lecture notes), Chapter 4 "Keplerian orbits", Section 4.16 "Binary star systems", https://farside.ph.utexas.edu/teaching/celestial/Celestial/node38.html, Eqs. (4.108)-(4.119)

import Mathlib
import Definitions.Def_CelestialMechanics_binary_star_dynamics

namespace CelestialMechanics
theorem comFrame_positions (m₁ m₂ : ℝ) (r₁ r₂ : ℝ → Space)
    (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (hcom : ∀ t, m₁ • r₁ t + m₂ • r₂ t = 0) :
    (∀ t, r₁ t = (-(m₂ / (m₁ + m₂))) • (r₂ t - r₁ t)) ∧
    (∀ t, r₂ t = (m₁ / (m₁ + m₂)) • (r₂ t - r₁ t)) := by sorry
end CelestialMechanics
