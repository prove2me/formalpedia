-- Prove2me | Theorems.Thm_ClusterDecomp_algorithm_2_partition
-- name    : ClusterDecomp.algorithm_2_partition
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:09:17.564745+00:00
-- url     : https://prove2.me/theorems/f21e7b4b-94ef-402c-b99c-655b03bab0d3
-- title:
--   §3.2, p.15 — Algorithm 2 returns a partition with $B_i\subseteq P_i$
-- statement:
--   Let $B_1,\dots,B_k$ be pairwise disjoint sets of positive volume, $k\ge2$, and let $P_1,\dots,P_k$ be returned by Algorithm 2. Then
--   $$V=P_1\sqcup\dots\sqcup P_k,\qquad B_i\subseteq P_i\ \text{ for every }i\in[k].$$
--
--   No backbone is ever split, since each is contracted into one terminal at each node.
--
--   Differences from the source:
--   - generalization: integer weights with polynomial ratio (standing assumption, p.1) → any symmetric nonnegative real weights, with no positive-degree assumption; reason: the argument uses neither integrality, the ratio nor positive degrees; the graphs of the paper are instances
--   - generalization: B_1, …, B_k are the backbones output by Algorithm 1 (§3.2, p.14: "We assume that B1, . . . , Bk are the output of Algorithm 1") → any pairwise disjoint B_1, …, B_k of positive volume; reason: the argument uses only the disjointness of the backbones and the fairness of the cuts of Algorithm 2; Algorithm 1 outputs are an instance (Lemma 3.2 gives positive volume, B_i ⊆ A_i disjointness)
--   - encoding: "the partition returned by Algorithm 2" → every recursion tree with every balanced split and every α_a-fair cut (Alg2Run); reason: the paper fixes nothing beyond balance and fairness; the relation covers every execution
-- source:
--   Sun, Zhang, Zhou, Faster Cluster Decomposition with Stronger Bi-Criteria Guarantee, STOC 2027 submission (manuscript sha256 ba091f54…), §3.2, p.15 (PDF p.17)

import Mathlib
import Definitions.Def_ClusterDecomp_Alg2Run

open Finset
open scoped ENNReal

namespace ClusterDecomp

/-- **The output of Algorithm 2 is a partition.**

Sun, Zhang, Zhou, *Faster Cluster Decomposition with Stronger Bi-Criteria Guarantee*, STOC 2027 submission
(manuscript sha256 ba091f54…), §3.2, p.15 (PDF p.17).

"Note that since all backbones indexed by IuL are contracted into s and all backbones indexed by IuR are contracted into t, no backbone is ever split.
Moreover, the two resulting child subsets XuL and XuR partition Xu, and the sets P1, . . . , Pk returned by Algorithm 2 satisfy
V = P1 ⊔ · · · ⊔ Pk, Bi ⊆ Pi for every i ∈ [k]."

For every run of Algorithm 2 on pairwise disjoint positive-volume backbones. -/
theorem algorithm_2_partition {V : Type*} [Fintype V] [DecidableEq V] (G : WGraph V) {k : ℕ} (hk : 2 ≤ k)
    (B : Fin k → Finset V) (hB : Pairwise fun a b => Disjoint (B a) (B b))
    (hB0 : ∀ i, 0 < G.vol (B i)) {P : Fin k → Finset V} (hP : Alg2Run G B P) :
    (Pairwise fun a b => Disjoint (P a) (P b)) ∧ univ.biUnion P = univ ∧ ∀ i, B i ⊆ P i := by sorry

end ClusterDecomp
