-- Prove2me | Theorems.Thm_Brouwer_injOn_image_add_smul_closedBall
-- name    : Brouwer.injOn_image_add_smul_closedBall
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-27T00:30:10.254714+00:00
-- url     : https://prove2.me/theorems/565938b8-813e-4509-a569-f9ccf9683167
-- title:
--   A small Lipschitz perturbation of the identity permutes the closed unit ball
-- statement:
--   Let $\bar B \subset \mathbb{R}^d$ be the closed unit ball with boundary sphere $S$. Let
--   $h$ be $L$-Lipschitz on $\bar B$, vanish on $S$, and keep the ball invariant in the sense that
--   $x + h(x) \in \bar B$ for every $x \in \bar B$. For a parameter $t$ with $0 \le t \le 1$ and
--   $tL < 1$, consider the perturbation of the identity
--
--   $$
--   \varphi_t(x) \;=\; x + t\,h(x).
--   $$
--
--   Then $\varphi_t$ is injective on $\bar B$ and maps it *onto* itself:
--
--   $$
--   \varphi_t|_{\bar B} \ \text{is injective} \qquad\text{and}\qquad \varphi_t(\bar B) \;=\; \bar B .
--   $$
--
--   So for small enough $t$ the perturbed map is a bijection of the ball, not merely a self-map.
--   The condition $tL < 1$ is what makes the perturbation invertible, and surjectivity onto the
--   whole ball is the part that carries real information: it says the image cannot shrink. This is
--   the lemma that lets a volume or degree computation be run on $\varphi_t(\bar B)$ as if on
--   $\bar B$ itself.
-- source:
--   J. Milnor, Analytic proofs of the “hairy ball theorem” and the Brouwer fixed point theorem, Amer. Math. Monthly 85 (1978), 521–524, §1–§3; carved from the accepted proof of ChanPangGQVI.ProjExistence.theorem_5_2, https://prove2.me/submissions/08ed2756-557a-470f-8493-8c93e6b779c8

import Mathlib

open Metric Set MeasureTheory

theorem Brouwer.injOn_image_add_smul_closedBall {d : ℕ} (h : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (L : NNReal)
    (hL : LipschitzOnWith L h (closedBall 0 1))
    (h0 : ∀ x ∈ sphere (0 : EuclideanSpace ℝ (Fin d)) 1, h x = 0)
    (hB : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, x + h x ∈ closedBall 0 1)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (htL : t * L < 1) :
    InjOn (fun x => x + t • h x) (closedBall 0 1) ∧
      (fun x => x + t • h x) '' closedBall 0 1 = closedBall 0 1 := by sorry
