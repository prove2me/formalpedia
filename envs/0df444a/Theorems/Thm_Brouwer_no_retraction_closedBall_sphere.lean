-- Prove2me | Theorems.Thm_Brouwer_no_retraction_closedBall_sphere
-- name    : Brouwer.no_retraction_closedBall_sphere
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-27T00:30:22.075875+00:00
-- url     : https://prove2.me/theorems/25abe5d2-8437-4826-a8e8-d123f0fb033b
-- title:
--   No smooth retraction of the closed ball onto its boundary sphere
-- statement:
--   Let $d \ge 1$, let $\bar B \subset \mathbb{R}^d$ be the closed unit ball and $S$ its
--   boundary sphere. There is **no** continuously differentiable retraction of the ball onto its
--   boundary. Precisely, suppose $U$ is an open set containing $\bar B$ and $r : U \to \mathbb{R}^d$
--   is of class $C^1$ with
--
--   $$
--   r(\bar B) \subseteq S \qquad\text{and}\qquad r(x) = x \ \text{ for every } x \in S .
--   $$
--
--   Then no such $r$ exists: the hypotheses are contradictory.
--
--   The sphere is not a smooth retract of the ball, and this is the central obstruction from which
--   Brouwer's fixed point theorem follows: a self-map of the ball without a fixed point would
--   produce exactly such a retraction. Stated on its own it is also the natural input for degree-
--   and index-type arguments, which is why it is worth having separately from the fixed point
--   theorem itself.
--
--   **Formalization Note** The $C^1$ hypothesis is `ContDiffOn ℝ 1 r U` on an open
--   $U \supseteq \bar B$, and the conclusion is `False`.
-- source:
--   J. Milnor, Analytic proofs of the “hairy ball theorem” and the Brouwer fixed point theorem, Amer. Math. Monthly 85 (1978), 521–524, §1–§3; carved from the accepted proof of ChanPangGQVI.ProjExistence.theorem_5_2, https://prove2.me/submissions/08ed2756-557a-470f-8493-8c93e6b779c8

import Mathlib

open Metric Set MeasureTheory

theorem Brouwer.no_retraction_closedBall_sphere {d : ℕ} (hd : 0 < d)
    (r : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (U : Set (EuclideanSpace ℝ (Fin d))) (hU : IsOpen U) (hBU : closedBall 0 1 ⊆ U)
    (hr : ContDiffOn ℝ 1 r U)
    (hmaps : MapsTo r (closedBall 0 1) (sphere 0 1))
    (hid : ∀ x ∈ sphere (0 : EuclideanSpace ℝ (Fin d)) 1, r x = x) : False := by sorry
