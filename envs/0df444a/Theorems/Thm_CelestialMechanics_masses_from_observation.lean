-- Prove2me | Theorems.Thm_CelestialMechanics_masses_from_observation
-- name    : CelestialMechanics.masses_from_observation
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T18:27:08.730238+00:00
-- url     : https://prove2.me/theorems/c7d847a9-a913-47da-b03e-681771059bca
-- title:
--   Measuring a binary: $m_1+m_2 = 4\pi^2a^3/(GT^2)$ and $m_1\lVert\mathbf{r}_1\rVert = m_2\lVert\mathbf{r}_2\rVert$
-- statement:
--   **Determining the two stellar masses (closing paragraph of Section 4.16).** Two observable quantities fix the masses of a binary system.
--
--   First, inverting the period relation (4.116) gives the *sum* of the masses from the measured major radius $a$ and period $T$:
--
--   $$ m_1+m_2 = \frac{4\pi^{2}a^{3}}{G\,T^{2}}. $$
--
--   Second, in the center-of-mass frame the two stars are always on opposite sides of the origin and their distances from it are in the fixed inverse ratio of their masses,
--
--   $$ m_1\,\lVert\mathbf{r}_1(t)\rVert = m_2\,\lVert\mathbf{r}_2(t)\rVert, \qquad\text{i.e.}\qquad \frac{m_1}{m_2} = \frac{\lVert\mathbf{r}_2(t)\rVert}{\lVert\mathbf{r}_1(t)\rVert}, $$
--
--   so the observed ratio of the apparent orbits gives the *ratio* of the masses. Sum and ratio together determine $m_1$ and $m_2$ individually.
-- source:
--   Richard Fitzpatrick, *Celestial Mechanics* (University of Texas at Austin, lecture notes), Chapter 4 "Keplerian orbits", Section 4.16 "Binary star systems", https://farside.ph.utexas.edu/teaching/celestial/Celestial/node38.html, Eqs. (4.108)-(4.119)

import Mathlib
import Definitions.Def_CelestialMechanics_binary_star_dynamics

namespace CelestialMechanics
theorem masses_from_observation (G m₁ m₂ a T : ℝ) (r₁ r₂ : ℝ → Space)
    (hG : 0 < G) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (ha : 0 < a) (hT : 0 < T)
    (hper : T = Real.sqrt (4 * Real.pi ^ 2 * a ^ 3 / (G * (m₁ + m₂))))
    (hcom : ∀ t, m₁ • r₁ t + m₂ • r₂ t = 0) :
    m₁ + m₂ = 4 * Real.pi ^ 2 * a ^ 3 / (G * T ^ 2) ∧
    ∀ t, m₁ * ‖r₁ t‖ = m₂ * ‖r₂ t‖ := by sorry
end CelestialMechanics
