-- Prove2me | Theorems.Thm_DynamicsRelativity_conic_ecc_lt_one_isEllipse
-- name    : DynamicsRelativity.conic_ecc_lt_one_isEllipse
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-22T23:20:35.172641+00:00
-- url     : https://prove2.me/theorems/81f26438-34d9-4247-a673-5b2fc9b70798
-- title:
--   A conic of eccentricity $e < 1$ is an ellipse with a focus at the origin
-- statement:
--   This is the geometric half of Kepler's first law: Tong's passage from the polar equation (4.14) to the Cartesian equation (4.15) of an ellipse.
--
--   Work inside the plane through the origin with normal $n\neq0$, and let $A$ be a vector of that plane with $\lVert A\rVert<1$, and $r_0>0$. Consider the conic with focus at the origin, semi-latus rectum $r_0$ and eccentricity $e=\lVert A\rVert$,
--
--   $$ C \;=\; \big\{\, y \;:\; \langle n,y\rangle = 0,\quad \lVert y\rVert + \langle A, y\rangle = r_0 \,\big\}, $$
--
--   which in polar coordinates of that plane, with $\theta$ measured from the direction of $A$, is $r = r_0/(1+e\cos\theta)$. Then $C$ is an **ellipse with the origin as one of its two foci**: there are a second focus $c$ in the same plane and a number $a$ with $\lVert c\rVert<2a$ such that $C$ consists exactly of the points $y$ of the plane with $\lVert y\rVert+\lVert y-c\rVert = 2a$.
--
--   The source obtains the same conclusion by squaring $r = r_0 - e\,x$ and completing the square, arriving at $(x-x_c)^{2}/a^{2}+y^{2}/b^{2}=1$ with the centre displaced from the origin by $\lvert x_c\rvert = ea$; the origin, where the star sits, is a focus of that ellipse. The statement here is the coordinate-free form of that conclusion. The case $A=0$ is included and gives a circle.
--
--   This milestone is pure geometry: it mentions no trajectory and no equation of motion, and it is the only step of the argument that is independent of the dynamics.
-- source:
--   David Tong, Dynamics and Relativity, University of Cambridge Part IA Mathematical Tripos lecture notes, Lent 2013, http://www.damtp.cam.ac.uk/user/tong/relativity.html — §4.3.1, "Ellipses: $e<1$", eq. (4.15) and the surrounding discussion, pp. 57–58 ("The origin where the star sits … is called the focus of the ellipse").

import Definitions.Def_DynamicsRelativity_CentralForces_Defs
import Mathlib

open DynamicsRelativity

theorem DynamicsRelativity.conic_ecc_lt_one_isEllipse {n A : Vec} {r₀ : ℝ}
    (hn : n ≠ 0) (hnA : inner ℝ n A = 0) (hr₀ : 0 < r₀) (hA : ‖A‖ < 1) :
    IsEllipseWithFocusAtOrigin {y : Vec | inner ℝ n y = 0 ∧ ‖y‖ + inner ℝ A y = r₀} := by
  sorry
