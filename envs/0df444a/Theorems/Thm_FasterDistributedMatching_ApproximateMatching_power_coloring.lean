-- Prove2me | Theorems.Thm_FasterDistributedMatching_ApproximateMatching_power_coloring
-- name    : FasterDistributedMatching.ApproximateMatching.power_coloring
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-17T15:53:40.218184+00:00
-- url     : https://prove2.me/theorems/924f73db-a534-4a16-b19f-8a3106ee9894
-- title:
--   Computing a proper coloring of the line-graph power
-- statement:
--   For each fixed polynomial identifier convention, there are a deterministic physical LOCAL program and constants $C>0$ and $a\ge1$, chosen before the graph inputs, such that for every $\ell\ge2$ the program produces endpoint-consistent edge colors properly coloring $L(G)^{256\ell+1}$. Its palette and round bounds are
--
--   $$\#\text{colors}\le\max\{2,\Delta\}^{a\ell},\qquad T\le\left\lceil C\ell\max\{1,\log^*n\}\right\rceil.$$
--
--   The only local inputs are the physical vertex identifier and its neighbor identifiers, together with the common bounds and $\ell$. This is the algorithmic coloring component of Lemma 3.3. It supplies colors that can subsequently be transferred to arbitrary virtual copies by a separate geometric lemma.
-- source:
--   Mohsen Ghaffari and Christoph Grunau, Faster Deterministic Distributed Matching: Breaking the Log-Squared Barrier, STOC 2027 submission #1024, Lemma 3.3 and Appendix A, printed pp.9 and 22 / PDF pp.11 and 24; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1024.pdf

import Definitions.Def_FasterDistributedMatching_ApproximateMatching_Routing

namespace FasterDistributedMatching.ApproximateMatching
theorem power_coloring :
    ∀ b : ℕ, ∃ (A : Deterministic (Bounds × ℕ) (Finset ℕ) (ℕ → ℕ)) (C : ℝ) (a : ℕ),
      0 < C ∧ 1 ≤ a ∧
      (∀ k ell, 2 ≤ ell → A.program.rounds (k,ell) ≤ budget C (ell * (logStar k.n : ℝ))) ∧
      ∀ (N : ℕ) (G : SimpleGraph (Fin N)) (k : Bounds) (ell : ℕ),
        2 ≤ ell → boundedGraph G k.n k.degree →
        ∀ ids : Fin N → ℕ, Identifiers k.n (b + 1) ids →
          ∃ chi : Sym2 (Fin N) → ℕ,
            (∀ u v, G.Adj u v →
              execute A G (k,ell) ids (neighborIDs G ids) u (ids v) = chi s(u,v) ∧
              execute A G (k,ell) ids (neighborIDs G ids) v (ids u) = chi s(u,v)) ∧
            Proper (graphPower (lineGraph G) (256 * ell + 1))
              ((max 2 k.degree) ^ (a * ell)) (fun e => chi e.val) := by sorry
end FasterDistributedMatching.ApproximateMatching
