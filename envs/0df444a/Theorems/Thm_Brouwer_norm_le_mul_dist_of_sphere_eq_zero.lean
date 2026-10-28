-- Prove2me | Theorems.Thm_Brouwer_norm_le_mul_dist_of_sphere_eq_zero
-- name    : Brouwer.norm_le_mul_dist_of_sphere_eq_zero
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-27T00:30:10.471086+00:00
-- url     : https://prove2.me/theorems/62000936-b14d-4610-9e17-7c396c3c8111
-- title:
--   A Lipschitz field vanishing on the sphere is bounded by the distance to the ball
-- statement:
--   Let $\bar B = \{x \in \mathbb{R}^d : \|x\| \le 1\}$ be the closed unit ball and
--   $S = \{x : \|x\| = 1\}$ its boundary sphere. Let $h : \mathbb{R}^d \to \mathbb{R}^d$ be
--   $L$-Lipschitz on $\bar B$ for some constant $L \ge 0$, and suppose $h$ vanishes on $S$, that
--   is $h(x) = 0$ for every $x \in S$. Then for every $x \in \bar B$ and every $z \notin \bar B$,
--
--   $$
--   \|h(x)\| \;\le\; L\,\|x - z\| .
--   $$
--
--   The point of the inequality is that the bound involves a point $z$ *outside* the ball, where
--   $h$ is not assumed to satisfy anything: a field that dies on the boundary is controlled by the
--   distance to the complement of the ball. This is what makes such a field extendable to the whole
--   space without losing its Lipschitz constant, which is the first step in the perturbation
--   argument for the no-retraction theorem.
-- source:
--   J. Milnor, Analytic proofs of the “hairy ball theorem” and the Brouwer fixed point theorem, Amer. Math. Monthly 85 (1978), 521–524, §1–§3; carved from the accepted proof of ChanPangGQVI.ProjExistence.theorem_5_2, https://prove2.me/submissions/08ed2756-557a-470f-8493-8c93e6b779c8

import Mathlib

open Metric Set MeasureTheory

theorem Brouwer.norm_le_mul_dist_of_sphere_eq_zero {d : ℕ} (h : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (L : NNReal) (hL : LipschitzOnWith L h (closedBall 0 1))
    (h0 : ∀ x ∈ sphere (0 : EuclideanSpace ℝ (Fin d)) 1, h x = 0)
    {x z : EuclideanSpace ℝ (Fin d)} (hx : x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1)
    (hz : z ∉ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) :
    ‖h x‖ ≤ L * dist x z := by sorry
