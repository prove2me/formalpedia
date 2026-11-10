-- Prove2me | Theorems.Thm_FasterDistributedMatching_ApproximateMatching_theorem_1_1
-- name    : FasterDistributedMatching.ApproximateMatching.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T12:10:24.264845+00:00
-- url     : https://prove2.me/theorems/b8fb9268-9461-4268-9535-0dee6586d769
-- title:
--   Theorem 1.1 — deterministic LOCAL (1 + epsilon)-approximate maximum matching
-- statement:
--   For every positive real $\varepsilon$ and every finite undirected simple graph $G$, with known vertex and degree bounds $|V(G)|\le n$ and $\deg(G)\le\Delta$, a uniform deterministic LOCAL protocol returns an actual matching $M$ satisfying
--
--   $$\operatorname{OPT}(G)\le(1+\varepsilon)|M|.$$
--
--   For each fixed polynomial identifier-range convention there are constants $C>0$ and $d\in\mathbb N$, chosen before accuracy, graph, bounds and identifiers, such that
--
--   $$T\le\left\lceil C(1+1/\varepsilon)^d\left(L^{3/2}J^2+\sqrt L\max\{1,\log^*n\}\right)\right\rceil,$$
--
--   where $L=\max\{1,\log_2(\max\{2,\Delta\})\}$ and $J=\max\{1,\log_2L\}$. Nodes initially know their identifier, neighbor identifiers, the common bounds and $\varepsilon$; no bipartition, matching oracle or optimum is supplied. Both endpoints report their incident matching edge consistently. The protocol must work for every permitted injective identifier assignment, and includes empty graphs, isolated vertices, small degrees and all $\varepsilon>1$.
--
--   This is the source's complete degree-dependent headline result, including the square-root factor in the additive coloring term and polynomial accuracy overhead. The external approximation booster remains a proof obligation, not a hypothesis.
--
--   Differences from the source:
--   - encoding: finite undirected simple graphs → SimpleGraph (Fin N), with arbitrary supplied bounds n and degree; reason: every finite simple graph can be relabelled in this way; the carrier index is never processor input
--   - encoding: deterministic synchronous LOCAL algorithms → tape-independent published LocalAlg programs with source-only local inputs and endpoint-consistent outputs; reason: rules and types precede graph inputs; multiset broadcast supports addressed dictionaries without bandwidth restrictions
--   - encoding: asymptotic base-two logarithmic bounds → uniform positive constants, natural ceiling budgets and logarithms padded to at least one; reason: only bounded-parameter conventions change; empty and degree-zero or degree-one graphs remain included
--   - encoding: unique O(log n)-bit identifiers → every injection below max(2,n)^(b+1), for each fixed natural b; reason: the protocol and constants may depend on the fixed ID convention, and never on a graph, its identifiers or epsilon
--   - encoding: hidden poly(1/epsilon) overhead for all epsilon > 0 → a uniform C(1+1/epsilon)^d factor, with natural d and C>0 before epsilon; reason: this expresses polynomial accuracy overhead explicitly and includes large epsilon without narrowing its domain
-- source:
--   Mohsen Ghaffari, Christoph Grunau, STOC 2027 submission #1024 (October 2026), Theorem 1.1, printed pp.1–2, PDF pp.3–4; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1024.pdf

import Mathlib
import Definitions.Def_FasterDistributedMatching_ApproximateMatching_Local

namespace FasterDistributedMatching.ApproximateMatching

/- Theorem 1.1, printed pp.1--2 / PDF pp.3--4; §3.5. The program and polynomial
accuracy bound precede all graph instances and all positive real epsilon. -/
theorem theorem_1_1 :
    ∀ b : ℕ, ∃ (A : Deterministic Accuracy (Finset ℕ) (Option ℕ)) (C : ℝ) (d : ℕ),
      0 < C ∧
      (∀ k : Accuracy, 0 < k.epsilon →
        A.program.rounds k ≤ budget C ((1 + 1 / k.epsilon) ^ d * matchingTime k.n k.degree)) ∧
      ∀ (N : ℕ) (G : SimpleGraph (Fin N)) (k : Accuracy),
        0 < k.epsilon → boundedGraph G k.n k.degree →
        ∀ ids : Fin N → ℕ, Identifiers k.n (b + 1) ids →
          ∃ M : SimpleGraph (Fin N),
            ReportsMatching G ids (execute A G k ids (neighborIDs G ids)) M ∧
            (optimum G : ℝ) ≤ (1 + k.epsilon) * (matchingSize M : ℝ) := by sorry

end FasterDistributedMatching.ApproximateMatching
