-- Prove2me | Theorems.Thm_Brouwer_exists_contDiff_approx
-- name    : Brouwer.exists_contDiff_approx
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-27T00:30:26.299829+00:00
-- url     : https://prove2.me/theorems/f99ca1b1-7707-4561-8e85-d0e0201733a0
-- title:
--   Uniform `C¹` approximation of a continuous vector field on the ball
-- statement:
--   Let $\bar B \subset \mathbb{R}^d$ be the closed unit ball and let
--   $f : \bar B \to \mathbb{R}^d$ be continuous. Then for every $\delta > 0$ there is a map
--   $G : \mathbb{R}^d \to \mathbb{R}^d$ of class $C^1$ on all of $\mathbb{R}^d$ with
--
--   $$
--   \sup_{x \in \bar B} \bigl\|G(x) - f(x)\bigr\| \;<\; \delta .
--   $$
--
--   This is the vector-valued form of uniform smooth approximation on the ball. Together with a
--   theorem about $C^1$ self-maps it yields the corresponding theorem about continuous self-maps,
--   which is how Brouwer's fixed point theorem is obtained in full generality from its smooth
--   case.
-- source:
--   Smooth approximation of a continuous map on a compact set; cf. C. A. Rogers, A less strange version of Milnor’s proof of Brouwer’s fixed-point theorem, Amer. Math. Monthly 87 (1980), 525–527. Carved from the accepted proof of ChanPangGQVI.ProjExistence.theorem_5_2, https://prove2.me/submissions/08ed2756-557a-470f-8493-8c93e6b779c8

import Mathlib

open Metric Set MeasureTheory

theorem Brouwer.exists_contDiff_approx {d : ℕ}
    (f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hf : ContinuousOn f (closedBall 0 1)) (δ : ℝ) (hδ : 0 < δ) :
    ∃ G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d), ContDiff ℝ 1 G ∧
      ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, ‖G x - f x‖ < δ := by sorry
