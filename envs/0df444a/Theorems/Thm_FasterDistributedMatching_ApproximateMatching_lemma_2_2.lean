-- Prove2me | Theorems.Thm_FasterDistributedMatching_ApproximateMatching_lemma_2_2
-- name    : FasterDistributedMatching.ApproximateMatching.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T12:14:11.298875+00:00
-- url     : https://prove2.me/theorems/78c50071-ac58-4c50-b081-1c65303b8dc3
-- title:
--   Lemma 2.2 — pairwise local derandomization
-- statement:
--   In a finite variable graph, each variable has a finite label set and a probability distribution. Every positive probability is at least $\lambda\in(0,1/2]$. Let $U,C$ be sums of nonnegative unary or adjacent-pair tables, locally known at their incident processors, and let $U(p),C(p)$ be expectations under independent label choices. Given a proper $\zeta$-coloring and
--
--   $$U(p)-C(p)\ge\tfrac12 U(p),$$
--
--   one deterministic LOCAL protocol chooses only labels with positive initial probability and returns $s$ satisfying
--
--   $$U(s)-C(s)\ge\tfrac9{10}(U(p)-C(p))$$
--
--   in $O((\log_2(1/\lambda))^2+\log_2(1/\lambda)\max\{1,\log^*\zeta\})$ variable-graph rounds, with a uniform constant. The empty variable graph is included; each nonempty variable's label support is nonempty by normalization.
--
--   This gives the source's utility-cost derandomization guarantee. No expectation or resulting assignment is supplied as processor input.
--
--   Differences from the source:
--   - encoding: finite undirected simple graphs → SimpleGraph (Fin N), with arbitrary supplied bounds n and degree; reason: every finite simple graph can be relabelled in this way; the carrier index is never processor input
--   - encoding: deterministic synchronous LOCAL algorithms → tape-independent published LocalAlg programs with source-only local inputs and endpoint-consistent outputs; reason: rules and types precede graph inputs; multiset broadcast supports addressed dictionaries without bandwidth restrictions
--   - encoding: asymptotic base-two logarithmic bounds → uniform positive constants, natural ceiling budgets and logarithms padded to at least one; reason: only bounded-parameter conventions change; empty and degree-zero or degree-one graphs remain included
--   - generalization: unique O(log n)-bit identifiers → all injective natural-number identifiers, with one protocol and uniform time constant; reason: the initialization, gathering, coloring-based derandomization or cleanup uses only comparisons or supplied colors; polynomial-range identifiers are included
--   - encoding: finite labels and independent expectations → finite sets of natural names, ordered incident tables and exact product-weighted finite sums; reason: arbitrary finite labels can be renamed; multiple local terms can be aggregated; unused entries are masked to zero
-- source:
--   Mohsen Ghaffari, Christoph Grunau, STOC 2027 submission #1024 (October 2026), Lemma 2.2, printed p.7, PDF p.9; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1024.pdf

import Mathlib
import Definitions.Def_FasterDistributedMatching_ApproximateMatching_Routing

namespace FasterDistributedMatching.ApproximateMatching

/- Lemma 2.2, printed p.7 / PDF p.9. The source fraction is 1/2, not 12.
All expectations are genuine finite sums with normalized probability weights. -/
theorem lemma_2_2 :
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

end FasterDistributedMatching.ApproximateMatching
