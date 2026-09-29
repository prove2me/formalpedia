-- Prove2me | Theorems.Thm_CelestialMechanics_conic_solves_kepler
-- name    : CelestialMechanics.conic_solves_kepler
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T18:23:14.050303+00:00
-- url     : https://prove2.me/theorems/d283b1e0-530c-40a2-b1f8-7485b9824e7e
-- title:
--   Eqs. (4.112)-(4.115): the conic $r = a(1-e^2)/(1+e\cos\theta)$ with $\dot\theta = h/r^2$ solves the Kepler problem
-- statement:
--   **Equations (4.112)-(4.115).** Fix $G>0$, $M>0$, a major radius $a>0$, an eccentricity $0\le e<1$ and an angular momentum per unit reduced mass $h>0$ related to $a$ by Eq. (4.115),
--
--   $$ a = \frac{h^{2}}{(1-e^{2})\,G M}, \qquad\text{equivalently}\qquad h^{2} = (1-e^{2})\,G M a. $$
--
--   Let $\theta$ be a differentiable function of time and let the planar curve
--
--   $$ \mathbf{r}(t) = \bigl(\rho(t)\cos\theta(t),\ \rho(t)\sin\theta(t),\ 0\bigr), \qquad \rho(t) = \frac{a(1-e^{2})}{1+e\cos\theta(t)}, \qquad \dot\theta(t) = \frac{h}{\rho(t)^{2}} $$
--
--   be the corresponding conic. Then $\mathbf{r}$ is an exact solution of the relative Kepler equation (4.110): it is twice continuously differentiable, never zero, and
--
--   $$ \ddot{\mathbf{r}} = -\frac{G M}{\lVert\mathbf{r}\rVert^{3}}\,\mathbf{r}. $$
--
--   This is the analytic core of the section: it is the statement that the ellipse of Eq. (4.113), traversed at the rate prescribed by conservation of angular momentum, really solves Newton's equation of motion.
-- source:
--   Richard Fitzpatrick, *Celestial Mechanics* (University of Texas at Austin, lecture notes), Chapter 4 "Keplerian orbits", Section 4.16 "Binary star systems", https://farside.ph.utexas.edu/teaching/celestial/Celestial/node38.html, Eqs. (4.108)-(4.119)

import Mathlib
import Definitions.Def_CelestialMechanics_binary_star_dynamics

namespace CelestialMechanics
theorem conic_solves_kepler (G M a e h : ℝ) (rad th : ℝ → ℝ) (r : ℝ → Space)
    (hG : 0 < G) (hM : 0 < M) (ha : 0 < a) (he0 : 0 ≤ e) (he1 : e < 1)
    (hh : 0 < h) (hha : h ^ 2 = (1 - e ^ 2) * G * M * a)
    (horb : IsConicOrbit a e h rad th r) :
    IsKeplerRelative G M r := by sorry
end CelestialMechanics
