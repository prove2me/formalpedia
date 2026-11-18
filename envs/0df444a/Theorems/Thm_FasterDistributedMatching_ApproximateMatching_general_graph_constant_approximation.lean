-- Prove2me | Theorems.Thm_FasterDistributedMatching_ApproximateMatching_general_graph_constant_approximation
-- name    : FasterDistributedMatching.ApproximateMatching.general_graph_constant_approximation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-17T22:35:30.996799+00:00
-- url     : https://prove2.me/theorems/f347e4cf-80f8-48d4-b5cf-fb27c27f707a
-- title:
--   Constant approximation in arbitrary graphs via the bipartite cover
-- statement:
--   For arbitrary finite simple graphs, the bipartite approximation algorithm extends to a uniform deterministic LOCAL constant approximation with the same communication bound.
--
--   There is an absolute constant $c>0$ such that, for every fixed polynomial identifier convention, there are a deterministic LOCAL protocol and a constant $C>0$, fixed before the network inputs, with the following property. For a graph $G$ with supplied vertex and degree bounds $n,\Delta$ and distinct identifiers below $\max\{2,n\}^{b+1}$, the protocol returns an actual matching $M$ and satisfies
--
--   $$
--   c\,\operatorname{OPT}(G)\le |M|,
--   \qquad
--   T\le\left\lceil C\left(L^{3/2}J^2+\sqrt L\,\max\{1,\log^* n\}\right)\right\rceil,
--   $$
--
--   where $L=\max\{1,\log_2\max\{2,\Delta\}\}$ and $J=\max\{1,\log_2 L\}$. Each endpoint reports its partner's identifier, and the endpoint reports agree. No bipartition is supplied.
--
--   This is the general-graph matching oracle used by the approximation booster in Section 3.5.
-- source:
--   Ghaffari--Grunau, Faster Deterministic Distributed Matching: Breaking the Log-Squared Barrier, STOC 2027 submission #1024 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1024.pdf, Section 3.5, proof of Theorem 1.1, printed pp.14--15 / PDF pp.16--17, bipartite-cover and projection paragraphs.

import Mathlib
import Definitions.Def_FasterDistributedMatching_ApproximateMatching_Local
open FasterDistributedMatching.ApproximateMatching

theorem FasterDistributedMatching.ApproximateMatching.general_graph_constant_approximation :
    ∃ c : ℝ, 0 < c ∧ ∀ b : ℕ,
      ∃ (A : Deterministic Bounds (Finset ℕ) (Option ℕ)) (C : ℝ),
        0 < C ∧
        (∀ k : Bounds, A.program.rounds k ≤ budget C (matchingTime k.n k.degree)) ∧
        ∀ (N : ℕ) (G : SimpleGraph (Fin N)) (k : Bounds),
          boundedGraph G k.n k.degree →
          ∀ ids : Fin N → ℕ, Identifiers k.n (b+1) ids →
            ∃ M : SimpleGraph (Fin N),
              ReportsMatching G ids (execute A G k ids (neighborIDs G ids)) M ∧
              c*(optimum G:ℝ) ≤ (matchingSize M:ℝ) := by sorry
