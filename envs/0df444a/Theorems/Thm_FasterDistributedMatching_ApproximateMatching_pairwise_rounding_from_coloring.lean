-- Prove2me | Theorems.Thm_FasterDistributedMatching_ApproximateMatching_pairwise_rounding_from_coloring
-- name    : FasterDistributedMatching.ApproximateMatching.pairwise_rounding_from_coloring
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-17T18:18:07.188654+00:00
-- url     : https://prove2.me/theorems/ab044a36-030b-4fd6-bc21-c110d85f9b62
-- title:
--   Pairwise LOCAL rounding from a weighted defective-coloring protocol
-- statement:
--   Assume a deterministic LOCAL protocol $W$ and a positive absolute integer $B$ provide the following weighted-coloring primitive: from any proper $\zeta$-coloring of a finite graph with symmetric nonnegative incident weights, and every integer $Q\ge2$, the protocol uses at most $B(Q+\max\{1,\log^*\zeta\})$ physical rounds, outputs fewer than $BQ$ colors, and leaves at most a $4/Q$ fraction of total edge weight monochromatic.
--
--   Consider a finite variable graph. Each variable has a finite label set and a normalized distribution whose positive probabilities are at least $\lambda\in(0,1/2]$. Let $U$ and $C$ be sums of nonnegative unary terms and terms on adjacent variable pairs. Incident tables and initial distributions are locally supplied, together with a proper $\zeta$-coloring. Write $\mathbb E$ for independent initial label choices. If
--
--   $$
--   \mathbb E U-\mathbb E C\ge\tfrac12\mathbb E U,
--   $$
--
--   then there is one deterministic LOCAL rounding protocol and a positive constant $C_0$, fixed before the precision and all graph inputs, which choose only labels of positive initial probability and return an assignment $s$ satisfying
--
--   $$
--   U(s)-C(s)\ge\tfrac9{10}(\mathbb E U-\mathbb E C)
--   $$
--
--   within
--
--   $$
--   \left\lceil C_0\left(\log_2^2(1/\lambda)+\log_2(1/\lambda)\max\{1,\log^*\zeta\}\right)\right\rceil
--   $$
--
--   physical communication rounds. Arbitrary injective identifiers are allowed. The primitive is the only algorithmic assumption: this conditional result isolates the rounding construction and analysis so it can be combined with any implementation of weighted defective coloring.
--
--   **Formalization Note** Ordered incident pair tables may be asymmetric; both orientations are included in the objective and locally supplied. Expectations are finite product sums over the actual label sets. This item is the black-box reduction implicit in Algorithms 1–2, Lemmas 2.1–2.3, and the weighted-coloring implementation in the cited paper.
-- source:
--   Faour, Ghaffari, Grunau, Kuhn, Rozhon, Local Distributed Rounding: Generalized to MIS, Matching, Set Cover, and Beyond, https://arxiv.org/abs/2209.11651v1. Algorithms1–2 and Lemmas2.1–2.3 pp.14–19 (PDF16–21), together with weighted-coloring implementation in proof Lemma2.6 pp.22–24; black-box algorithm construction specialized to constant loss 1/10 and utility gap1/2. Also Ghaffari–Grunau, STOC2027 submission1024, Lemma2.2 printedp.7/PDF9, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1024.pdf.

import Definitions.Def_DistributedRounding_WeightedColoring
open FasterDistributedMatching.ApproximateMatching

theorem FasterDistributedMatching.ApproximateMatching.pairwise_rounding_from_coloring
    (W : Deterministic (ℕ × ℕ) DistributedRounding.WeightedInput ℕ) (B : ℕ)
    (hB : 0 < B)
    (hTime : ∀ Q zeta, 2 ≤ Q → W.program.rounds (Q,zeta) ≤ B*(Q+logStar zeta))
    (hColor : ∀ (N : ℕ) (H : SimpleGraph (Fin N)) (ids : Fin N → ℕ)
      (weights : Fin N → ℕ → ℝ) (col : Fin N → ℕ) (Q zeta : ℕ),
      2 ≤ Q → Proper H zeta col →
      (∀ v u, 0 ≤ weights v (ids u)) →
      (∀ v u, weights v (ids u) = weights u (ids v)) →
      let out := execute W H (Q,zeta) ids (fun v => (weights v,col v))
      (∀ v, out v < B*Q) ∧
      (Q:ℝ)*DistributedRounding.monochromatic H (fun v u => weights v (ids u)) out ≤
        4*(∑ v, DistributedRounding.incident H (fun v u => weights v (ids u)) v)) :
    ∃ (A : Deterministic (ℝ × ℕ) ObjectiveInput ℕ) (C : ℝ), 0 < C ∧
      (∀ lambda zeta, 0 < lambda → lambda ≤ 1 / 2 →
        A.program.rounds (lambda,zeta) ≤ budget C
          ((logTwo (1 / lambda)) ^ 2 + logTwo (1 / lambda) * (logStar zeta : ℝ))) ∧
      ∀ (N : ℕ) (D : PairwiseInstance N) (lambda : ℝ) (zeta : ℕ)
        (col : Fin N → ℕ), ValidObjective D lambda → Proper D.graph zeta col →
        finiteExpectation D (utility D) - finiteExpectation D (cost D) ≥
          (1 / 2) * finiteExpectation D (utility D) →
        ∀ ids : Fin N → ℕ, Function.Injective ids →
          let s := execute A D.graph (lambda,zeta) ids (objectiveInput D ids col)
          (∀ v, s v ∈ D.labels v ∧ 0 < D.probability v (s v)) ∧
          utility D s - cost D s ≥
            (9 / 10) * (finiteExpectation D (utility D) - finiteExpectation D (cost D)) := by sorry
