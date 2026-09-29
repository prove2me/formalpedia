-- Prove2me | Theorems.Thm_CelestialMechanics_two_body_reduction
-- name    : CelestialMechanics.two_body_reduction
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T18:21:24.703975+00:00
-- url     : https://prove2.me/theorems/66b86c91-ee9a-4a1e-9a66-e51322aa4057
-- title:
--   Reduction of the binary system to a one-body Kepler problem ($\ddot{\mathbf{r}} = -GM\mathbf{r}/r^3$, $M=m_1+m_2$)
-- statement:
--   **Equations (4.109)-(4.111).** In a Newtonian gravitational two-body system with positive masses $m_1, m_2$, the relative separation $\mathbf{r}=\mathbf{r}_2-\mathbf{r}_1$ obeys the equation of motion of a single fictitious body moving in the gravitational field of a fixed mass $M = m_1+m_2$:
--
--   $$ \frac{d^{2}\mathbf{r}}{dt^{2}} = -\frac{G M}{r^{3}}\,\mathbf{r}, \qquad M = m_1+m_2, $$
--
--   where $r=\lVert\mathbf{r}\rVert$. Equivalently, dividing Newton's two equations of motion by the respective masses and subtracting, the reduced mass $\mu=m_1m_2/(m_1+m_2)$ cancels and the relative motion decouples from the motion of the center of mass. The conclusion also records that the relative separation is twice continuously differentiable and never vanishes.
-- source:
--   Richard Fitzpatrick, *Celestial Mechanics* (University of Texas at Austin, lecture notes), Chapter 4 "Keplerian orbits", Section 4.16 "Binary star systems", https://farside.ph.utexas.edu/teaching/celestial/Celestial/node38.html, Eqs. (4.108)-(4.119)

import Mathlib
import Definitions.Def_CelestialMechanics_binary_star_dynamics

namespace CelestialMechanics
theorem two_body_reduction (G m₁ m₂ : ℝ) (r₁ r₂ : ℝ → Space)
    (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (h : IsNewtonianTwoBody G m₁ m₂ r₁ r₂) :
    IsKeplerRelative G (m₁ + m₂) (fun t => r₂ t - r₁ t) := by sorry
end CelestialMechanics
