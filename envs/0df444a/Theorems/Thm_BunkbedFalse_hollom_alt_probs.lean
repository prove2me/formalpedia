-- Prove2me | Theorems.Thm_BunkbedFalse_hollom_alt_probs
-- name    : BunkbedFalse.hollom_alt_probs
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-11T16:58:14.473518+00:00
-- url     : https://prove2.me/theorems/0479c1be-daf4-448d-8e11-066ba0daa936
-- title:
--   Lemma 3.1 (Hollom) — $12/64$ vs $13/64$
-- statement:
--   Let $H$ be Hollom's $3$-uniform hypergraph on $u_1, \dots, u_{10}$ with six hyperedges, and let $T = \{u_2, u_7, u_9\}$ be its transversal set. Consider the **alternative** bunkbed hypergraph percolation, in which each hyperedge is retained on exactly one of the two levels, chosen by a fair coin. Then
--
--   $$\mathbb{P}^{\mathrm{alt}}\bigl[u_1 \leftrightarrow u_{10}\bigr] = \frac{12}{64}, \qquad \mathbb{P}^{\mathrm{alt}}\bigl[u_1 \leftrightarrow u'_{10}\bigr] = \frac{13}{64}.$$
--
--   In particular the bunkbed inequality fails for hypergraphs: crossing to the other level is *more* likely than staying. This is Hollom's refutation of the $3$-uniform hypergraph version of the conjecture, and it is the seed of the whole construction — though it does not by itself settle the graph case, since a hyperedge cannot be simulated exactly by bond percolation.
--
--   **Formalization Note** There are exactly $2^6 = 64$ configurations, which is why both probabilities have denominator $64$; the source calls the computation "small enough to be checked by hand". One caveat for solvers: Mathlib's decision procedure for `SimpleGraph.Reachable` enumerates walks and is far too slow to close this by `decide` on the $20$-vertex bunkbed. A linear-time reachability procedure, together with a proof that it agrees with `Reachable`, is the recommended route and is reusable elsewhere.
-- source:
--   N. Gladkov, I. Pak, A. Zimin, "The bunkbed conjecture is false", Proc. Natl. Acad. Sci. USA 122 (2025), no. 24, e2420725122, https://doi.org/10.1073/pnas.2420725122 - p. 2, Lemma 3.1, quoting Hollom (arXiv:2406.01790, Claim 5.1).

import Definitions.Def_BunkbedHypergraph
open Bunkbed Bunkbed.Hyper SimpleGraph Finset

namespace BunkbedFalse

/-- **Lemma 3.1** (Hollom; quoted p. 2). In the alternative bunkbed hypergraph percolation on
Hollom's hypergraph, `ℙᵃˡᵗ[u₁ ↔ u₁₀] = 12/64` while `ℙᵃˡᵗ[u₁ ↔ u'₁₀] = 13/64`. -/
theorem hollom_alt_probs :
    altProb hollomE hollomT ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) = 12 / 64 ∧
    altProb hollomE hollomT ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) = 13 / 64 := by
  sorry

end BunkbedFalse
