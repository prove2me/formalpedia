-- Prove2me | Theorems.Thm_ClusterDecomp_lemma_3_7
-- name    : ClusterDecomp.lemma_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:09:23.415203+00:00
-- url     : https://prove2.me/theorems/4f9cb1c6-6aea-43ee-adcc-967670c1aab5
-- title:
--   Lemma 3.7, p.15 — $w(Y,P_i\setminus Y)\ge\frac1{2\sqrt e\,k}w(Y,V\setminus Y)$
-- statement:
--   Let $P_1\sqcup\dots\sqcup P_k$ be returned by Algorithm 2 on pairwise disjoint sets $B_1,\dots,B_k$ of positive volume, $k\ge2$. For every $i\in[k]$ and $Y\subseteq P_i\setminus B_i$,
--   $$w(Y,P_i\setminus Y)\ge\frac1{2\sqrt e\,k}\,w(Y,V\setminus Y).$$
--
--   So a set outside the backbone sends a $1/O(k)$ share of its boundary inside its own part; this is the source of the linear dependence on $k$.
--
--   Differences from the source:
--   - generalization: integer weights with polynomial ratio (standing assumption, p.1) → any symmetric nonnegative real weights, with no positive-degree assumption; reason: the argument uses neither integrality, the ratio nor positive degrees; the graphs of the paper are instances
--   - generalization: B_1, …, B_k are the backbones output by Algorithm 1 (§3.2, p.14: "We assume that B1, . . . , Bk are the output of Algorithm 1") → any pairwise disjoint B_1, …, B_k of positive volume; reason: the argument uses only the disjointness of the backbones and the fairness of the cuts of Algorithm 2; Algorithm 1 outputs are an instance (Lemma 3.2 gives positive volume, B_i ⊆ A_i disjointness)
--   - encoding: "the partition returned by Algorithm 2" → every recursion tree with every balanced split and every α_a-fair cut (Alg2Run); reason: the paper fixes nothing beyond balance and fairness; the relation covers every execution
-- source:
--   Sun, Zhang, Zhou, Faster Cluster Decomposition with Stronger Bi-Criteria Guarantee, STOC 2027 submission (manuscript sha256 ba091f54…), Lemma 3.7, p.15 (PDF p.17)

import Mathlib
import Definitions.Def_ClusterDecomp_Alg2Run

open Finset
open scoped ENNReal

namespace ClusterDecomp

/-- **Lemma 3.7.**

Sun, Zhang, Zhou, *Faster Cluster Decomposition with Stronger Bi-Criteria Guarantee*, STOC 2027 submission
(manuscript sha256 ba091f54…), Lemma 3.7, p.15 (PDF p.17).

"Let P1 ⊔ · · · ⊔ Pk be the partition returned by Algorithm 2. Then, it holds for any i ∈ [k] and Y ⊆ Pi ∖ Bi that
w(Y, Pi ∖ Y) ≥ (1/(2√e k)) · w(Y, V ∖ Y)."

For every run of Algorithm 2, every balanced split and every fair cut; no conductance hypothesis on the backbones is needed. -/
theorem lemma_3_7 {V : Type*} [Fintype V] [DecidableEq V] (G : WGraph V) {k : ℕ} (hk : 2 ≤ k)
    (B : Fin k → Finset V) (hB : Pairwise fun a b => Disjoint (B a) (B b))
    (hB0 : ∀ i, 0 < G.vol (B i)) {P : Fin k → Finset V} (hP : Alg2Run G B P) (i : Fin k)
    (Y : Finset V) (hY : Y ⊆ P i \ B i) :
    1 / (2 * Real.sqrt (Real.exp 1) * k) * G.cut Y Yᶜ ≤ G.cut Y (P i \ Y) := by sorry

end ClusterDecomp
