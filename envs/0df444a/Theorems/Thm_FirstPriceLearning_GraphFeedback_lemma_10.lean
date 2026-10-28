-- Prove2me | Theorems.Thm_FirstPriceLearning_GraphFeedback_lemma_10
-- name    : FirstPriceLearning.GraphFeedback.lemma_10
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T06:27:52.107068+00:00
-- url     : https://prove2.me/theorems/fa147b28-6e67-4761-960b-db94dbf53388
-- title:
--   Lemma 10 (as in [ACBDK15]) — a weakly dominating set of size at most 50α log n
-- statement:
--   Let $G = (V, E)$ be a directed graph with $n \ge 2$ vertices and independence number at most $\alpha$. Then there is a set $S \subseteq V$ of vertices with
--   $$
--   |S| \le 50\,\alpha\log n
--   $$
--   such that every vertex of $G$ is in $S$ or is a child of some vertex of $S$.
--
--   In the language of Remark 4, the weak domination number satisfies $\delta(G) \le 50\,\alpha(G)\log n$. The paper quotes this from Alon, Cesa-Bianchi, Dekel and Koren (2015, Lemma 8). It is the graph-theoretic input of Theorem 3 with Option I: in every round the chosen vertex of largest out-degree removes at least a $1/(50\alpha\log K)$ fraction of the least-pulled actions.
--
--   **Formalization Note** As printed, "every vertex of $G$ is a child of some vertex in $V$" with $n$ unrestricted, the lemma is false: for $n = 1$ the bound is $50\alpha\log 1 = 0$, and in an edgeless graph no vertex is anyone's child. The formalization uses the reading of the cited source and of Theorem 3's proof: vertices of $S$ count as dominated, and $n \ge 2$. $\log$ is the natural logarithm.
-- source:
--   Han, Zhou, Weissman, Optimal No-regret Learning in Repeated First-price Auctions, arXiv:2003.09795v7, p. 35, Lemma 10 (quoting Alon, Cesa-Bianchi, Dekel, Koren 2015, Lemma 8) and Remark 4

import Mathlib
import Definitions.Def_FirstPriceLearning_GraphFeedback_FeedbackGraph

namespace FirstPriceLearning.GraphFeedback

/-- Lemma 10 (p. 35, quoted from Alon, Cesa-Bianchi, Dekel and Koren 2015, Lemma 8), in the
source's reading: a directed graph on `n ≥ 2` vertices with independence number at most `α` has a
weakly dominating set `V` — every vertex is in `V` or is a child of a vertex of `V` — with
`|V| ≤ 50 α log n`. -/
theorem lemma_10 (n : ℕ) (hn : 2 ≤ n) (E : Fin n → Fin n → Prop) (α : ℕ)
    (hα : IndepNumberLE E α) :
    ∃ V : Finset (Fin n), (V.card : ℝ) ≤ 50 * α * Real.log n ∧ IsWeaklyDominating E V := by sorry

end FirstPriceLearning.GraphFeedback
