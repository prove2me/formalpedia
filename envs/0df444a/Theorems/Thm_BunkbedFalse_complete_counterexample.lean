-- Prove2me | Theorems.Thm_BunkbedFalse_complete_counterexample
-- name    : BunkbedFalse.complete_counterexample
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-10-01T00:50:06.881751+00:00
-- url     : https://prove2.me/theorems/2ba48618-cbce-4edb-b568-1a45d5379ddd
-- title:
--   Theorem 6.1 — counterexample to the complete bunkbed conjecture
-- statement:
--   There exists a finite connected simple graph $G=(V,E)$ with
--   $$|V|<10^6,\qquad |E|<10^6,$$
--   and vertices $u,v\in V$ such that independent bond percolation with retention probability $1/2$ on the Cartesian product $G\times K_2$ satisfies
--   $$\mathbb P_{1/2}(u_0\leftrightarrow v_0)<\mathbb P_{1/2}(u_0\leftrightarrow v_1).$$
--   Every horizontal edge and every vertical edge is independently retained with probability $1/2$. In particular, the complete bunkbed conjecture is false.
--
--   **Formalization Note.** The vertex set is represented by $\{0,\ldots,n-1\}$, and the edge bound counts the edges of the resulting simple graph. The connection probabilities are exact finite rational sums.
-- source:
--   N. Gladkov, I. Pak, A. Zimin, The bunkbed conjecture is false, PNAS 122 (2025), e2420725122, https://www.math.ucla.edu/~pak/papers/Bunkbed-PNAS.pdf#page=9, Section 6, Theorem 6.1.

import Definitions.Def_BunkbedComplete
open Bunkbed Finset SimpleGraph

theorem BunkbedFalse.complete_counterexample :
    ∃ (n : ℕ) (E : Finset (Sym2 (Fin n))) (u v : Fin n),
      n < 1000000 ∧ (ofEdges E).edgeFinset.card < 1000000 ∧
      (ofEdges E).Connected ∧
      completeProb E (1 / 2) (u, 0) (v, 0) <
        completeProb E (1 / 2) (u, 0) (v, 1) := by sorry
