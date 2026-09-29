-- Prove2me | Theorems.Thm_Finset_popular_pairs_card_lower_bound
-- name    : Finset.popular_pairs_card_lower_bound
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-17T06:31:18.040806+00:00
-- url     : https://prove2.me/theorems/27820583-617e-48fa-9f9f-1dd8a12fc99e
-- title:
--   Large energy implies many popular pairs
-- statement:
--   Let $G$ be an additive commutative group and $X, Y \subseteq G$ finite sets with $X$ nonempty and $|X| = |Y|$. Suppose $$E(X, Y) \ge \eta\, |X|^3 \qquad (\eta > 0),$$ where $E(X,Y) = \sum_s r_{X,Y}(s)^2$ is the additive energy and $r_{X,Y}(s) = X.\mathrm{addConvolution}\, Y\, s$ counts representations $s = x+y$. If $\theta : \mathbb{N}$ satisfies $2\theta \le \eta\,|X|$, then the popular pairs are numerous: $$\#\{(x, y) \in X \times Y : r_{X,Y}(x+y) \ge \theta\} \ge \tfrac{\eta}{2}\,|X|\,|Y|.$$ The proof splits the energy sum into popular and unpopular fibres and uses the total-mass identity $\sum_s r(s) = |X||Y|$. This lemma quantifies the first half of the energy-to-graph conversion: truncating the convolution at level $\theta$ retains a constant fraction of all pairs, so that together with the Markov upper bound on the number of popular sums it produces the dense popular-sum graph.
-- source:
--   Popular/unpopular fibre split inside the proof of Tao-Vu, Additive Combinatorics, Cambridge Univ. Press (2006), Lemma 2.30 (p. 80). Not separately stated in the cited work. Formalized in https://github.com/mysticflounder/lean-formalizations/blob/dd46c17a2a034d7bfa0df02e7f77834d35592864/lean/LeanFormalizations/Combinatorics/Additive/BalogSzemerediGowers.lean#L121-L213

import Mathlib

open scoped Pointwise

theorem Finset.popular_pairs_card_lower_bound {G : Type*} [AddCommGroup G] [DecidableEq G]
    {η : ℝ} (_hη : 0 < η)
    {X Y : Finset G} (hXY : X.card = Y.card) (hX : X.Nonempty)
    (hE : η * (X.card : ℝ) ^ 3 ≤ (Finset.addEnergy X Y : ℝ))
    (θ : ℕ) (hθ : 2 * (θ : ℝ) ≤ η * X.card) :
    η / 2 * (X.card : ℝ) * Y.card ≤
      (((X ×ˢ Y).filter
        (fun p ↦ θ ≤ X.addConvolution Y (p.1 + p.2))).card : ℝ) := by sorry
