-- Prove2me | Theorems.Thm_CelestialMechanics_orbital_period
-- name    : CelestialMechanics.orbital_period
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T18:23:39.96148+00:00
-- url     : https://prove2.me/theorems/9bd1b5f9-0147-4ff3-ac5f-adf8306dcd67
-- title:
--   Eq. (4.116): $T = \sqrt{4\pi^2 a^3/(GM)}$ for the binary orbit
-- statement:
--   **Equation (4.116) — Kepler's third law for a binary system.** Consider the Keplerian conic of Eqs. (4.112)-(4.115) with $G,M,a,h>0$, $0\le e<1$ and $h^{2}=(1-e^{2})GMa$. If the true anomaly advances by one full turn between times $t_0$ and $t_0+T$, i.e. $\theta(t_0+T)=\theta(t_0)+2\pi$ with $T>0$, then the elapsed time is the orbital period
--
--   $$ T = \sqrt{\frac{4\pi^{2} a^{3}}{G M}}, \qquad\text{equivalently}\qquad n \equiv \frac{2\pi}{T} = \frac{\sqrt{G M}}{a^{3/2}} \quad\text{(Eq. 4.117)}. $$
--
--   The value depends on the major radius and the total mass only, not on the eccentricity nor on the starting angle $\theta(t_0)$.
-- source:
--   Richard Fitzpatrick, *Celestial Mechanics* (University of Texas at Austin, lecture notes), Chapter 4 "Keplerian orbits", Section 4.16 "Binary star systems", https://farside.ph.utexas.edu/teaching/celestial/Celestial/node38.html, Eqs. (4.108)-(4.119)

import Mathlib
import Definitions.Def_CelestialMechanics_binary_star_dynamics

namespace CelestialMechanics
theorem orbital_period (G M a e h T t₀ : ℝ) (rad th : ℝ → ℝ) (r : ℝ → Space)
    (hG : 0 < G) (hM : 0 < M) (ha : 0 < a) (he0 : 0 ≤ e) (he1 : e < 1)
    (hh : 0 < h) (hha : h ^ 2 = (1 - e ^ 2) * G * M * a)
    (horb : IsConicOrbit a e h rad th r)
    (hT : 0 < T) (hrev : th (t₀ + T) = th t₀ + 2 * Real.pi) :
    T = Real.sqrt (4 * Real.pi ^ 2 * a ^ 3 / (G * M)) := by sorry
end CelestialMechanics
