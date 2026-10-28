-- Prove2me | Theorems.Thm_Brouwer_exists_fixedPoint_closedBall_contDiff
-- name    : Brouwer.exists_fixedPoint_closedBall_contDiff
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-27T00:30:20.800506+00:00
-- url     : https://prove2.me/theorems/626c7295-ee88-4507-bae0-e8e15daaa277
-- title:
--   Brouwer’s fixed point theorem for continuously differentiable self-maps of the ball
-- statement:
--   Let $\bar B \subset \mathbb{R}^d$ be the closed unit ball and let
--   $f : \mathbb{R}^d \to \mathbb{R}^d$ be of class $C^1$ with $f(\bar B) \subseteq \bar B$. Then $f$
--   has a fixed point in the ball:
--
--   $$
--   \exists\, x \in \bar B \ \text{ such that } \ f(x) = x .
--   $$
--
--   This is Brouwer's fixed point theorem in the smooth case. It is the form in which the theorem is
--   actually proved — the continuous case is obtained from it by approximation — and it is
--   worth stating separately because a map arising as the gradient or the flow of a smooth problem
--   already satisfies the $C^1$ hypothesis, making the approximation step unnecessary.
-- source:
--   J. Milnor, Analytic proofs of the “hairy ball theorem” and the Brouwer fixed point theorem, Amer. Math. Monthly 85 (1978), 521–524, §1–§3; carved from the accepted proof of ChanPangGQVI.ProjExistence.theorem_5_2, https://prove2.me/submissions/08ed2756-557a-470f-8493-8c93e6b779c8

import Mathlib

open Metric Set MeasureTheory

theorem Brouwer.exists_fixedPoint_closedBall_contDiff {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hf : ContDiff ℝ 1 f) (hmaps : MapsTo f (closedBall 0 1) (closedBall 0 1)) :
    ∃ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, f x = x := by sorry
