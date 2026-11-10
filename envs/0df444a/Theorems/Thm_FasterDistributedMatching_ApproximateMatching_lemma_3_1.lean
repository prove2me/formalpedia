-- Prove2me | Theorems.Thm_FasterDistributedMatching_ApproximateMatching_lemma_3_1
-- name    : FasterDistributedMatching.ApproximateMatching.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T12:10:23.197008+00:00
-- url     : https://prove2.me/theorems/d9c2840c-093e-4375-81ee-643ba8740844
-- title:
--   Lemma 3.1 — constant-approximate bipartite matching
-- statement:
--   For every finite simple bipartite graph $G$ with supplied bipartition and common bounds $|V(G)|\le n$ and maximum degree at most $\Delta$, there is a uniform deterministic LOCAL protocol returning an actual matching $M$ and a single absolute constant $c>0$ such that
--
--   $$|M|\ge c\,\operatorname{OPT}(G),\qquad
--   T=O\!\left((\log\Delta)^{3/2}(\log\log\Delta)^2+\sqrt{\log\Delta}\log^*n\right).$$
--
--   Both endpoints report the same matching edge, or no edge. The constant $c$ is chosen before the identifier convention as well as all graph instances; runtime constants may depend only on the fixed polynomial identifier convention. Initially nodes know their own side, neighbor identifiers and the common bounds. Empty graphs, isolated vertices and degrees zero and one remain included through positive logarithmic padding.
--
--   This is the bipartite constant-approximation oracle used in the source's full general-graph result.
--
--   Differences from the source:
--   - encoding: finite undirected simple graphs → SimpleGraph (Fin N), with arbitrary supplied bounds n and degree; reason: every finite simple graph can be relabelled in this way; the carrier index is never processor input
--   - encoding: deterministic synchronous LOCAL algorithms → tape-independent published LocalAlg programs with source-only local inputs and endpoint-consistent outputs; reason: rules and types precede graph inputs; multiset broadcast supports addressed dictionaries without bandwidth restrictions
--   - encoding: asymptotic base-two logarithmic bounds → uniform positive constants, natural ceiling budgets and logarithms padded to at least one; reason: only bounded-parameter conventions change; empty and degree-zero or degree-one graphs remain included
--   - encoding: unique O(log n)-bit identifiers → every injection below max(2,n)^(b+1), for each fixed natural b; reason: the protocol and constants may depend on the fixed ID convention, and never on a graph, its identifiers or epsilon
-- source:
--   Mohsen Ghaffari, Christoph Grunau, STOC 2027 submission #1024 (October 2026), Lemma 3.1, printed p.7, PDF p.9; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1024.pdf

import Mathlib
import Definitions.Def_FasterDistributedMatching_ApproximateMatching_Local

namespace FasterDistributedMatching.ApproximateMatching

/- Lemma 3.1, printed p.7 / PDF p.9, proof §§3.1--3.4.
The bipartition is part of each node's permitted local input. -/
theorem lemma_3_1 :
    ∃ c : ℝ, 0 < c ∧ ∀ b : ℕ,
      ∃ (A : Deterministic Bounds (Finset ℕ × Bool) (Option ℕ)) (C : ℝ), 0 < C ∧
      (∀ k, A.program.rounds k ≤ budget C (matchingTime k.n k.degree)) ∧
      ∀ (N : ℕ) (G : SimpleGraph (Fin N)) (k : Bounds), boundedGraph G k.n k.degree →
        ∀ side : Fin N → Bool, Bipartition G side →
        ∀ ids : Fin N → ℕ, Identifiers k.n (b + 1) ids →
          ∃ M : SimpleGraph (Fin N),
            ReportsMatching G ids
              (execute A G k ids (fun v => (neighborIDs G ids v, side v))) M ∧
            c * (optimum G : ℝ) ≤ (matchingSize M : ℝ) := by sorry

end FasterDistributedMatching.ApproximateMatching
