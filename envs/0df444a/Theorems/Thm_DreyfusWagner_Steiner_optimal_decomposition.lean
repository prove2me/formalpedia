-- Prove2me | Theorems.Thm_DreyfusWagner_Steiner_optimal_decomposition
-- name    : DreyfusWagner.Steiner.optimal_decomposition
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:06:11.658349+00:00
-- url     : https://prove2.me/theorems/4f9db6ad-e323-46bb-8613-3e8cd26e957f
-- title:
--   Optimal Decomposition Theorem — a Steiner tree splits at a node $p$ into Steiner trees for $\{p,q\}$, $\{p\} \cup D$, $\{p\} \cup (Y - D - \{q\})$
-- statement:
--   Let $G = (N, A)$ be a finite connected undirected graph whose arcs have positive lengths. Let $Y \subseteq N$ contain at least three nodes, let $S$ be a Steiner tree connecting $Y$, and let $q \in Y$. Then there exist a node $p \in N$ and a set $D \subseteq Y$ such that
--
--   1. $D$ is a nonempty proper subset of $Y - \{q\}$;
--   2. $S = S_1 \cup S_2 \cup S_3$ with $S_1, S_2, S_3$ pairwise disjoint;
--   3. $S_1$ is a Steiner path connecting $\{p, q\}$, $S_2$ is a Steiner path connecting $\{p\} \cup D$, and $S_3$ is a Steiner path connecting $\{p\} \cup (Y - D - \{q\})$.
--
--   The node $p$ need not belong to $Y$, may equal $q$ (then $S_1 = \emptyset$), and $S_3$ may be empty. In particular
--   $$|S| = D(p, q) + \operatorname{St}(\{p\} \cup D) + \operatorname{St}(\{p\} \cup (Y - D - \{q\})).$$
--
--   This is the structural fact behind the Dreyfus–Wagner dynamic program: an optimal tree for $Y$ is assembled from a shortest path and two optimal trees for strictly smaller terminal sets meeting at a junction node.
--
--   **Formalization Note** "$S$ consists of 3 disjoint subsets" is stated as $S = S_1 \cup S_2 \cup S_3$ with the three sets pairwise disjoint; no $S_i$ is required to be nonempty and $p$ is not required to lie outside $Y$, as in the paper's Figures 5 and 6. The hypothesis $\|Y\| \ge 3$ is the paper's own (Appendix A, p. 205).
-- source:
--   Dreyfus, Wagner, The Steiner Problem in Graphs, Networks 1 (1971), p. 206, Appendix A, Optimal Decomposition Theorem (also stated in §1, p. 197)

import Mathlib
import Definitions.Def_DreyfusWagner_Steiner_SteinerProblem

namespace DreyfusWagner.Steiner

/-- Dreyfus–Wagner 1971, Appendix A, Optimal Decomposition Theorem, p. 206 (also §1, p. 197). -/
theorem optimal_decomposition {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (ℓ : Sym2 V → ℝ)
    (hpos : ∀ e ∈ G.edgeSet, 0 < ℓ e) (hconn : G.Connected)
    (Y : Finset V) (S : Finset (Sym2 V)) (hS : IsSteinerTree G ℓ Y S)
    (q : V) (hq : q ∈ Y) (hY : 3 ≤ Y.card) :
    ∃ (p : V) (D : Finset V) (S₁ S₂ S₃ : Finset (Sym2 V)),
      D ⊆ Y.erase q ∧ D ≠ Y.erase q ∧ D.Nonempty ∧
      S = S₁ ∪ S₂ ∪ S₃ ∧ Disjoint S₁ S₂ ∧ Disjoint S₁ S₃ ∧ Disjoint S₂ S₃ ∧
      IsSteinerTree G ℓ {p, q} S₁ ∧
      IsSteinerTree G ℓ (insert p D) S₂ ∧
      IsSteinerTree G ℓ (insert p (Y.erase q \ D)) S₃ := by sorry

end DreyfusWagner.Steiner
