-- Prove2me | Theorems.Thm_DynamicsRelativity_kepler_first_law
-- name    : DynamicsRelativity.kepler_first_law
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-22T23:22:59.834707+00:00
-- url     : https://prove2.me/theorems/619b09f9-6b27-4c17-9bef-99279d48e9c2
-- title:
--   Kepler's first law: each planet moves in an ellipse with the Sun at one focus
-- statement:
--   **Kepler's first law (K1), the goal of this mission.** Each planet moves in an ellipse, with the Sun at one focus.
--
--   Let a particle of mass $m>0$ move in Euclidean $3$-space under the attractive inverse-square law of Tong's potential (4.12),
--
--   $$ m\,\ddot x(t) \;=\; -\,\frac{k\,m}{\lVert x(t)\rVert^{3}}\;x(t), \qquad k = GM > 0, $$
--
--   along a twice continuously differentiable trajectory that never reaches the centre of attraction. Assume that the angular momentum $L = m\,x\times\dot x$ does not vanish, and that the total energy
--
--   $$ E \;=\; \tfrac12 m\lVert\dot x\rVert^{2} - \frac{km}{\lVert x\rVert} $$
--
--   is negative. Then the whole trajectory lies on an **ellipse having the centre of attraction as one of its two foci**: there is a plane through the origin, a second focus $c$ in that plane and a number $a$ with $\lVert c\rVert < 2a$, such that every point $x(t)$ of the orbit satisfies
--
--   $$ \lVert x(t)\rVert + \lVert x(t) - c\rVert \;=\; 2a . $$
--
--   The two hypotheses beyond the equation of motion are the ones the source's own classification requires. Nonvanishing angular momentum excludes purely radial free-fall, whose trajectory is a segment and not an ellipse. Negative energy is the bounded regime, which by the energy–eccentricity relation (4.16) is exactly the case $e<1$; for $E>0$ the orbit is a hyperbola and for $E=0$ a parabola, neither of which is an ellipse.
--
--   This is the result that the whole of §4 builds to, and, as Tong observes, the one part of the derivation of Kepler's laws from the inverse-square law that was Newton's alone.
--
--   **Formalization Note.** The conclusion asserts that the image of the trajectory is *contained* in the ellipse; that a bounded orbit in fact traverses the entire ellipse is a separate statement, not claimed here.
-- source:
--   David Tong, Dynamics and Relativity, University of Cambridge Part IA Mathematical Tripos lecture notes, Lent 2013, http://www.damtp.cam.ac.uk/user/tong/relativity.html — §4.3.2, K1, p. 60 ("K1: Each planet moves in an ellipse, with the Sun at one focus"), together with the derivation in §4.3.1, eq. (4.14)–(4.16), pp. 56–60.

import Definitions.Def_DynamicsRelativity_CentralForces_Defs
import Mathlib

open DynamicsRelativity

theorem DynamicsRelativity.kepler_first_law {k m : ℝ} {x : ℝ → Vec}
    (hk : 0 < k) (h : KeplerMotion k m x) (hL : angularMomentum m x 0 ≠ 0)
    (hE : keplerEnergy k m x 0 < 0) :
    ∃ S : Set Vec, IsEllipseWithFocusAtOrigin S ∧ ∀ t, x t ∈ S := by sorry
