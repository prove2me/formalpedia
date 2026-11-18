-- Prove2me | Theorems.Thm_FasterDistributedMatching_ApproximateMatching_bounded_degree_bipartite_maximal_matching
-- name    : FasterDistributedMatching.ApproximateMatching.bounded_degree_bipartite_maximal_matching
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-17T21:51:32.744394+00:00
-- url     : https://prove2.me/theorems/f1bb7efa-5590-47c9-b46c-c91f96eb93c2
-- title:
--   Bounded-degree bipartite maximal matching in linear degree time
-- statement:
--   Let $H$ be a finite simple bipartite graph, with a supplied bipartition and maximum degree at most a common bound $D\ge0$. Processors have distinct natural identifiers and initially know their own side and their neighbors in $H$. There is one deterministic synchronous LOCAL protocol, uniform over all these inputs, that returns a maximal matching $M$ and satisfies
--
--   $$
--   T(D)\le 7(D+1).
--   $$
--
--   Both endpoints report their partner's identifier, or report no partner. Maximality means that every edge of $H$ has an endpoint incident to an edge of $M$.
--
--   The protocol may communicate in any supplied simple supergraph $G\supseteq H$, while its initial neighbor lists still describe only $H$. It filters received messages using those lists. This declared extension lets the matching routine operate directly on the support of a fractional assignment without changing the physical communication network. No bound on identifier magnitudes or on the degree of $G$ is required.
--
--   This is the bounded-degree bipartite extraction routine used in Section 3.4: setting $D=2^{16}$ makes its cost an absolute constant.
-- source:
--   Ghaffari--Grunau, Faster Deterministic Distributed Matching: Breaking the Log-Squared Barrier, STOC 2027 submission #1024, Section 3.4, printed p.14 / PDF p.16, paragraph "Extracting an integral matching from the constant-fractionality matching" (the O(D)-round bipartite maximal-matching routine cited to HKP98); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1024.pdf

import Mathlib
import Definitions.Def_FasterDistributedMatching_ApproximateMatching_Local
open FasterDistributedMatching.ApproximateMatching
open Classical

theorem FasterDistributedMatching.ApproximateMatching.bounded_degree_bipartite_maximal_matching :
    ∃ A : Deterministic ℕ (Finset ℕ × Bool) (Option ℕ),
      (∀ D, A.program.rounds D ≤ 7*(D+1)) ∧
      ∀ (N : ℕ) (G H : SimpleGraph (Fin N)) (D : ℕ), H ≤ G → (∀ v, H.degree v ≤ D) →
        ∀ side : Fin N → Bool, Bipartition H side →
          ∀ ids : Fin N → ℕ, Function.Injective ids → ∃ M : SimpleGraph (Fin N),
            ReportsMatching H ids (execute A G D ids (fun v => (neighborIDs H ids v,side v))) M ∧
            ∀ e ∈ H.edgeSet, ∃ v, v ∈ e ∧ ∃ w, M.Adj v w := by sorry
