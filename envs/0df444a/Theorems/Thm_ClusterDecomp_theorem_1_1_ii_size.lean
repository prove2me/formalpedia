-- Prove2me | Theorems.Thm_ClusterDecomp_theorem_1_1_ii_size
-- name    : ClusterDecomp.theorem_1_1_ii_size
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:09:31.341189+00:00
-- url     : https://prove2.me/theorems/6eccbfe0-d9f3-4795-89cf-2cec754da453
-- title:
--   Proof of Theorem 1.1(ii), p.18 — each level is disjoint with $\sum_u|E(G[X_u])|\le m$, and the depth is at most $\lceil\log_2k\rceil$
-- statement:
--   Let $T$ be a recursion tree of Algorithm 2 on pairwise disjoint sets $B_1,\dots,B_k$ of positive volume, $k\ge2$. Then at every level of $T$ the sets $X_u$ are pairwise disjoint and
--   $$\sum_u|E(G[X_u])|\le m,$$
--   and $T$ has depth at most $\lceil\log_2k\rceil$.
--
--   These two facts give the time $\widetilde O(m\log^2k)$ of Algorithm 2 once the black box is charged at each node.
--
--   Differences from the source:
--   - generalization: integer weights with polynomial ratio (standing assumption, p.1) → any symmetric nonnegative real weights, with no positive-degree assumption; reason: the argument uses neither integrality, the ratio nor positive degrees; the graphs of the paper are instances
--   - generalization: B_1, …, B_k are the backbones output by Algorithm 1 (§3.2, p.14: "We assume that B1, . . . , Bk are the output of Algorithm 1") → any pairwise disjoint B_1, …, B_k of positive volume; reason: the argument uses only the disjointness of the backbones and the fairness of the cuts of Algorithm 2; Algorithm 1 outputs are an instance (Lemma 3.2 gives positive volume, B_i ⊆ A_i disjointness)
--   - encoding: "the partition returned by Algorithm 2" → every recursion tree with every balanced split and every α_a-fair cut (Alg2Run); reason: the paper fixes nothing beyond balance and fairness; the relation covers every execution
--   - reading: the sentence also says that the time per level is Õ(mh) and the total is Õ(mh²) → only the combinatorial clauses are stated here; reason: the time parts are carried by theorem_1_1 and fair_cut_time on the machine; the milestone quotes only the combinatorial parts of the sentence
-- source:
--   Sun, Zhang, Zhou, Faster Cluster Decomposition with Stronger Bi-Criteria Guarantee, STOC 2027 submission (manuscript sha256 ba091f54…), proof of Theorem 1.1(ii), p.18 (PDF p.20)

import Mathlib
import Definitions.Def_ClusterDecomp_Alg2Run

open Finset
open scoped ENNReal

namespace ClusterDecomp

/-- **Proof of Theorem 1.1(ii): the recursion tree.**

Sun, Zhang, Zhou, *Faster Cluster Decomposition with Stronger Bi-Criteria Guarantee*, STOC 2027 submission
(manuscript sha256 ba091f54…), proof of Theorem 1.1(ii), p.18 (PDF p.20).

"Since all the Xu's in the same level of T are disjoint, we have Σu |E(G[Xu])| ≤ m and the algorithm's total running time at any fixed level is Õ(mh). Since T has
depth at most h = ⌈log2 k⌉, the total running time of Algorithm 2 is Õ(mh²) = Õ(m log2 k)."

The combinatorial content of this sentence, for every recursion tree: the nodes of a level are pairwise disjoint, `∑_u |E(G[X_u])| ≤ m` at every level, and the depth is at most `⌈log₂ k⌉`. The
time parts are carried by the goal `theorem_1_1`. -/
theorem theorem_1_1_ii_size {V : Type*} [Fintype V] [DecidableEq V] (G : WGraph V) {k : ℕ} (hk : 2 ≤ k)
    (B : Fin k → Finset V) (hB : Pairwise fun a b => Disjoint (B a) (B b))
    (hB0 : ∀ i, 0 < G.vol (B i)) {T : Tree k V} (hT : IsAlg2Tree G B T) :
    (∀ ℓ, (T.level ℓ).Pairwise Disjoint) ∧
      (∀ ℓ, ((T.level ℓ).map fun X => (G.edgesIn X).card).sum ≤ G.edges.card) ∧
      T.depth ≤ Nat.clog 2 k := by sorry

end ClusterDecomp
