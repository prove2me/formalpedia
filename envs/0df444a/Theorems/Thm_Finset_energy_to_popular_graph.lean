-- Prove2me | Theorems.Thm_Finset_energy_to_popular_graph
-- name    : Finset.energy_to_popular_graph
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-17T06:31:03.105241+00:00
-- url     : https://prove2.me/theorems/a18f1ef1-01a7-46cb-b155-cd8be50b1ff4
-- title:
--   Large energy yields a dense popular-sum graph
-- statement:
--   Let $G$ be an additive commutative group, let $\eta > 0$, and let $X, Y \subseteq G$ be finite sets with $X$ nonempty and $|X| = |Y|$ (so $Y$ is nonempty too; only the nonemptiness of $X$ is assumed). Assume the energy lower bound
--   $$E(X, Y) \ge \eta\, |X|^3$$
--   and the non-degeneracy condition $2 \le \tfrac{\eta}{2}\,|X|$. Then there exist a threshold $\theta : \mathbb{N}$ and a set of popular sums $S \subseteq G$ such that the graph of popular pairs is dense while $S$ is small:
--   $$\#\{(x, y) \in X \times Y : x + y \in S\} \ge \tfrac{\eta}{2}\,|X|\,|Y|, \qquad |S| \le \tfrac{4}{\eta}\,|X|,$$
--   where
--   $$S = \{s \in X + Y : r_{X,Y}(s) \ge \theta\}$$
--   and $r_{X,Y}(s) = X.\mathrm{addConvolution}\, Y\, s$ counts the representations $s = x + y$.
--
--   This is the entry point of the Balog-Szemeredi-Gowers pipeline: additive energy is converted, by a single threshold $\theta = \lfloor \tfrac{\eta}{2}|X| \rfloor$ on the representation function, into a dense bipartite graph $E \subseteq X \times Y$ whose restricted sumset $S$ is already controlled. The graph Balog-Szemeredi-Gowers theorem is then applied to $E$.
-- source:
--   Tao-Vu, Additive Combinatorics, Cambridge Univ. Press (2006), Lemma 2.30 (p. 80), converse half. Formalized for |X| = |Y| with K = 1/eta; the constant is 4/eta rather than the source's 2K = 2/eta (loss from rounding the popular threshold to an integer), and a largeness hypothesis 2 <= (eta/2)|X| is added so that threshold is at least one. Formalized in https://github.com/mysticflounder/lean-formalizations/blob/dd46c17a2a034d7bfa0df02e7f77834d35592864/lean/LeanFormalizations/Combinatorics/Additive/BSGEnergyToGraph.lean#L41-L150

import Mathlib

open scoped Pointwise

theorem Finset.energy_to_popular_graph {G : Type*} [AddCommGroup G] [DecidableEq G]
    {η : ℝ} (hη : 0 < η)
    {X Y : Finset G} (hX : X.Nonempty) (hXY : X.card = Y.card)
    (hLarge : 2 ≤ (η / 2) * (X.card : ℝ))
    (hE : η * (X.card : ℝ) ^ 3 ≤ (Finset.addEnergy X Y : ℝ)) :
    ∃ θ : ℕ, ∃ S : Finset G,
      (η / 2) * (X.card : ℝ) * Y.card ≤
        (((X ×ˢ Y).filter (fun p ↦ p.1 + p.2 ∈ S)).card : ℝ) ∧
      (S.card : ℝ) ≤ (4 / η) * (X.card : ℝ) ∧
      S = (X + Y).filter (fun s ↦ θ ≤ X.addConvolution Y s) := by sorry
