-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_far_crossing_coordinates_collision_extension
-- name    : BirkhoffGlobalSection.far_crossing_coordinates_collision_extension
-- status  : Proved
-- author  : @caleb
-- created : 2026-09-26T21:59:37.739442+00:00
-- url     : https://prove2.me/theorems/90e66d95-c803-41f1-ba56-e8151c1bd451
-- title:
--   Continuous extension of far-crossing coordinates at collision
-- statement:
--   Fix a real mass parameter $\mu$ and a collision state $s_0=(0,0,p_0,q_0)$ in Levi-Civita phase space with $p_0>0$ and $q_0<0$. Let $C_\mu$ denote the shooting coordinates (normalized vertical Jacobi velocity and depth). There exists a map $H$ from phase space to $\mathbb R^2$, continuous at $s_0$, such that
--   $$
--   H_2(s_0)=0,\qquad H_1(s_0)>\frac{\sqrt2}{2},
--   $$
--   and $H(s)=C_\mu(s)$ for every state $s=(z_0,z_1,p,q)$ with $z_1>0$ and $z_0=-z_1$.
--
--   This is an extension of the coordinates restricted to the far-crossing diagonal; it does not assert continuity of the physical velocity quotient in all phase-space directions at collision. An explicit choice, writing $\alpha=z_1$, is
--   $$
--   H(s)=\left(\frac{p-q-2\alpha\mu}{\sqrt{(8\alpha^3-p-q)^2+(p-q-2\alpha\mu)^2}},\;4\alpha^2\right).
--   $$
--   The result separates the elementary collision-coordinate limit from the dynamical problem of proving convergence to the collision state.
-- source:
--   Auxiliary coordinate lemma for Liu--Salomao, Finite energy foliations in the restricted three-body problem, https://arxiv.org/abs/2506.17867v2, Section 5, proof of Theorem 5.1 (far-family collision endpoint). Coordinate cancellation and strict-bound proof extracted and adapted from Mazecto's Prove2Me sketch https://prove2.me/submissions/e2fdab6a-c86e-45f3-8dcb-25889b3ea428; the displayed extension is an explicit algebraic derivation from the platform Levi-Civita coordinate definitions.

import Definitions.Def_BirkhoffShootingCoordinates
open BirkhoffGlobalSection

theorem BirkhoffGlobalSection.far_crossing_coordinates_collision_extension (μ : ℝ) (s₀ : Phase) (hz0 : s₀ 0 = 0) (hz1 : s₀ 1 = 0)
    (hp : 0 < s₀ 2) (hq : s₀ 3 < 0) :
    ∃ H : Phase → ℝ × ℝ, ContinuousAt H s₀ ∧ (H s₀).2 = 0 ∧
      Real.sqrt 2 / 2 < (H s₀).1 ∧
      ∀ s : Phase, 0 < s 1 → s 0 = -s 1 → shootingCoordinates μ s = H s := by sorry
