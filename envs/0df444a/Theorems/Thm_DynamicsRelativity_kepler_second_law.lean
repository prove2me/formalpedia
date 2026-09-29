-- Prove2me | Theorems.Thm_DynamicsRelativity_kepler_second_law
-- name    : DynamicsRelativity.kepler_second_law
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-22T23:18:19.768552+00:00
-- url     : https://prove2.me/theorems/aa1a1040-2fb6-408f-a89b-85392244b369
-- title:
--   Kepler's second law: equal areas in equal times
-- statement:
--   **Kepler's second law (K2).** The line between the planet and the Sun sweeps out equal areas in equal times.
--
--   Let a particle of mass $m>0$ move in an arbitrary central force field with radial profile $F$, and write $l=\lVert L\rVert/m$ for the angular momentum per unit mass, which in plane polar coordinates is Tong's conserved quantity $l=r^{2}\dot\theta$ of (4.5). The area swept by the radius vector between times $t_0$ and $t_1$ is
--
--   $$ A(t_0,t_1) \;=\; \frac{l}{2}\,(t_1-t_0), $$
--
--   so it depends on the elapsed time alone and not on when the interval begins — which is exactly the assertion of K2. The source obtains this from $\delta A=\tfrac12 r^{2}\delta\theta$, whence $dA/dt=\tfrac12 r^{2}\dot\theta=l/2$, a constant.
--
--   As Tong emphasizes, no property of the inverse-square law is used: Kepler's second law holds for *any* central force, and is nothing more than the conservation of angular momentum.
--
--   **Formalization Note.** The swept area is the invariant form $\tfrac12\int\lVert x\times\dot x\rVert\,dt$ of the source's area element.
-- source:
--   David Tong, Dynamics and Relativity, University of Cambridge Part IA Mathematical Tripos lecture notes, Lent 2013, http://www.damtp.cam.ac.uk/user/tong/relativity.html — §4.3.2, K2, p. 61 ("in time $\delta t$, the area swept out is $\delta A = \tfrac12 r^2\delta\theta$, so $dA/dt = \tfrac12 r^2\dot\theta = l/2$"); the conserved $l = r^2\dot\theta$ is eq. (4.5), p. 50.

import Definitions.Def_DynamicsRelativity_CentralForces_Defs
import Mathlib

open DynamicsRelativity

theorem DynamicsRelativity.kepler_second_law {m : ℝ} {F : ℝ → ℝ} {x : ℝ → Vec}
    (h : CentralForceMotion m F x) (t₀ t₁ : ℝ) :
    sweptArea x t₀ t₁ = (‖angularMomentum m x 0‖ / m) / 2 * (t₁ - t₀) := by sorry
