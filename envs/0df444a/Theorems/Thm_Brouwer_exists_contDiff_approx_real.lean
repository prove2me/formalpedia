-- Prove2me | Theorems.Thm_Brouwer_exists_contDiff_approx_real
-- name    : Brouwer.exists_contDiff_approx_real
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-27T00:30:25.901993+00:00
-- url     : https://prove2.me/theorems/93e99f7e-1451-4837-9ee0-586c09eb7861
-- title:
--   Uniform `C¹` approximation of a continuous real function on the ball
-- statement:
--   Let $\bar B \subset \mathbb{R}^d$ be the closed unit ball and let
--   $\varphi : \bar B \to \mathbb{R}$ be continuous. Then $\varphi$ can be approximated uniformly on
--   $\bar B$, to any accuracy, by a globally smooth function: for every $\eta > 0$ there is
--   $G : \mathbb{R}^d \to \mathbb{R}$ of class $C^1$ on all of $\mathbb{R}^d$ with
--
--   $$
--   \sup_{x \in \bar B} \bigl|G(x) - \varphi(x)\bigr| \;<\; \eta .
--   $$
--
--   The approximant is $C^1$ *everywhere*, not just on the ball, which is what makes it usable as
--   input to theorems stated for globally smooth maps. This is the scalar case of the approximation
--   step by which statements about smooth maps are transferred to continuous ones.
-- source:
--   Smooth approximation of a continuous function on a compact set; cf. C. A. Rogers, A less strange version of Milnor’s proof of Brouwer’s fixed-point theorem, Amer. Math. Monthly 87 (1980), 525–527. Carved from the accepted proof of ChanPangGQVI.ProjExistence.theorem_5_2, https://prove2.me/submissions/08ed2756-557a-470f-8493-8c93e6b779c8

import Mathlib

open Metric Set MeasureTheory

theorem Brouwer.exists_contDiff_approx_real {d : ℕ} (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hφ : ContinuousOn φ (closedBall 0 1)) (η : ℝ) (hη : 0 < η) :
    ∃ G : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ 1 G ∧
      ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, |G x - φ x| < η := by sorry
