-- Prove2me | Theorems.Thm_ClusterDecomp_theorem_1_1_i_size
-- name    : ClusterDecomp.theorem_1_1_i_size
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:09:42.592455+00:00
-- url     : https://prove2.me/theorems/9e495177-6cf0-4cb2-b096-88860bb4c92d
-- title:
--   Proof of Theorem 1.1(i), pp.13–14 — $\sum_i|E(H_{A_i})|\le5m$
-- statement:
--   Let $G$ have $m$ edges and positive degrees, and let $A_1,\dots,A_k$ be pairwise disjoint. Then $\sum_i|E(G[A_i])|\le m$, the number of positive-degree vertices contained in the $A_i$ is at most $2m$, and
--   $$\sum_{i=1}^k|E(H_{A_i})|\le\sum_{i=1}^k|E(G[A_i])|+4m\le5m.$$
--
--   This bound makes the total size of the auxiliary graphs linear, which is why Theorem 1.1(i) costs only $\widetilde O(m/\varepsilon)$.
--
--   Differences from the source:
--   - generalization: integer weights with polynomial ratio (standing assumption, p.1) → any symmetric nonnegative real weights with positive degrees; reason: the argument uses neither integrality nor the ratio, and integer weights are an instance
--   - encoding: |E(H_A)|, with zero-degree vertices omitted from H_A → |E(G[A])| + 2|A|, zero capacities included; reason: every vertex has positive degree (p.1), so no vertex is omitted
-- source:
--   Sun, Zhang, Zhou, Faster Cluster Decomposition with Stronger Bi-Criteria Guarantee, STOC 2027 submission (manuscript sha256 ba091f54…), proof of Theorem 1.1(i), pp.13–14 (PDF pp.15–16)

import Mathlib
import Definitions.Def_ClusterDecomp_Alg1Run

open Finset
open scoped ENNReal

namespace ClusterDecomp

/-- **Proof of Theorem 1.1(i): the size of the auxiliary graphs.**

Sun, Zhang, Zhou, *Faster Cluster Decomposition with Stronger Bi-Criteria Guarantee*, STOC 2027 submission
(manuscript sha256 ba091f54…), proof of Theorem 1.1(i), pp.13–14 (PDF pp.15–16).

"Since the sets A1, . . . , Ak are pairwise disjoint, we have Σ_{i=1}^k |E(G[Ai])| ≤ m and the total number of positive-degree vertices contained in the
Ai's is at most 2m. Hence, Σ_{i=1}^k |E(HAi)| ≤ Σ_{i=1}^k |E(G[Ai])| + 4m ≤ 5m."

Here `m = |E|`, and each link is a clause. `|E(H_A)|` is `numEdgesHA`, and loops count in `E` and `E(G[A])`. The paper omits zero-degree
vertices from `H_A`; under the standing assumption of p.1 there are none. -/
theorem theorem_1_1_i_size {V : Type*} [Fintype V] [DecidableEq V] (G : WGraph V) (hG : G.PosDeg) {k : ℕ}
    (A : Fin k → Finset V) (hA : Pairwise fun a b => Disjoint (A a) (A b)) :
    ∑ i, (G.edgesIn (A i)).card ≤ G.edges.card ∧
      ((univ.biUnion A).filter fun v => 0 < G.deg v).card ≤ 2 * G.edges.card ∧
      ∑ i, numEdgesHA G (A i) ≤ ∑ i, (G.edgesIn (A i)).card + 4 * G.edges.card ∧
      ∑ i, (G.edgesIn (A i)).card + 4 * G.edges.card ≤ 5 * G.edges.card := by sorry

end ClusterDecomp
