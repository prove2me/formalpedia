-- Prove2me | Theorems.Thm_Brouwer_lipschitzWith_ball_indicator
-- name    : Brouwer.lipschitzWith_ball_indicator
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-27T00:30:11.167623+00:00
-- url     : https://prove2.me/theorems/e03f5f8c-b8fb-4dfd-8571-e24f63c23567
-- title:
--   Extending a Lipschitz field by zero off the ball keeps it Lipschitz
-- statement:
--   Let $\bar B \subset \mathbb{R}^d$ be the closed unit ball with boundary sphere $S$, and
--   let $h : \mathbb{R}^d \to \mathbb{R}^d$ be $L$-Lipschitz on $\bar B$ with $h = 0$ on $S$. Define
--   the extension of $h$ by zero,
--
--   $$
--   \tilde h(x) \;=\; \begin{cases} h(x), & x \in \bar B,\\[2pt] 0, & x \notin \bar B.\end{cases}
--   $$
--
--   Then $\tilde h$ is $L$-Lipschitz on all of $\mathbb{R}^d$ — the same constant, with no loss.
--
--   Extending a boundary-vanishing field by zero is the standard way to turn a statement about the
--   ball into a statement about the whole space, so that global tools (Lipschitz inverse function
--   arguments, measure-theoretic change of variables) apply. Note that no continuity assumption is
--   needed off the ball; the hypothesis $h|_S = 0$ supplies it.
--
--   **Formalization Note** The extension is written as `Set.indicator` of the closed ball, so the
--   conclusion is `LipschitzWith` on the ambient space rather than `LipschitzOnWith`.
-- source:
--   J. Milnor, Analytic proofs of the “hairy ball theorem” and the Brouwer fixed point theorem, Amer. Math. Monthly 85 (1978), 521–524, §1–§3; carved from the accepted proof of ChanPangGQVI.ProjExistence.theorem_5_2, https://prove2.me/submissions/08ed2756-557a-470f-8493-8c93e6b779c8

import Mathlib

open Metric Set MeasureTheory

theorem Brouwer.lipschitzWith_ball_indicator {d : ℕ} (h : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (L : NNReal) (hL : LipschitzOnWith L h (closedBall 0 1))
    (h0 : ∀ x ∈ sphere (0 : EuclideanSpace ℝ (Fin d)) 1, h x = 0) :
    LipschitzWith L ((closedBall (0 : EuclideanSpace ℝ (Fin d)) 1).indicator h) := by sorry
