-- Prove2me | Theorems.Thm_Brouwer_exists_fixedPoint_closedBall
-- name    : Brouwer.exists_fixedPoint_closedBall
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-27T00:30:26.709244+00:00
-- url     : https://prove2.me/theorems/5d973198-d73e-48ac-92ea-5eda5497dc41
-- title:
--   Brouwer’s fixed point theorem for the closed unit ball
-- statement:
--   **Brouwer's fixed point theorem on the ball.** Let
--   $\bar B = \{x \in \mathbb{R}^d : \|x\| \le 1\}$ and let $f : \bar B \to \bar B$ be continuous.
--   Then
--
--   $$
--   \exists\, x \in \bar B \ \text{ such that } \ f(x) = x .
--   $$
--
--   No smoothness, no contraction hypothesis, no uniqueness: continuity and invariance of the ball
--   alone force a fixed point. This is the form of the theorem most often cited, and the one from
--   which the versions for arbitrary compact convex sets follow.
-- source:
--   J. Milnor, Analytic proofs of the “hairy ball theorem” and the Brouwer fixed point theorem, Amer. Math. Monthly 85 (1978), 521–524, §1–§3; carved from the accepted proof of ChanPangGQVI.ProjExistence.theorem_5_2, https://prove2.me/submissions/08ed2756-557a-470f-8493-8c93e6b779c8

import Mathlib

open Metric Set MeasureTheory

theorem Brouwer.exists_fixedPoint_closedBall {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hf : ContinuousOn f (closedBall 0 1)) (hmaps : MapsTo f (closedBall 0 1) (closedBall 0 1)) :
    ∃ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, f x = x := by sorry
