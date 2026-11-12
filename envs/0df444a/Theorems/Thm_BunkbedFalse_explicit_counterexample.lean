-- Prove2me | Theorems.Thm_BunkbedFalse_explicit_counterexample
-- name    : BunkbedFalse.explicit_counterexample
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-11T16:59:09.421625+00:00
-- url     : https://prove2.me/theorems/8fabe7f0-a20f-4baa-a5ac-39619039d4e4
-- title:
--   Theorem 1.2 — explicit counterexample on 7,222 vertices (planarity omitted)
-- statement:
--   There exists a connected graph $G = (V,E)$ with $|V| = 7{,}222$ vertices and $|E| = 14{,}442$ edges, a transversal set $T \subset V$ with exactly three vertices, and vertices $u, v \in V$, such that in bunkbed percolation at $P = 1/2$,
--
--   $$\mathbb{P}^{\mathrm{bb}}_{1/2}\bigl[u \leftrightarrow v\bigr] \;<\; \mathbb{P}^{\mathrm{bb}}_{1/2}\bigl[u \leftrightarrow v'\bigr].$$
--
--   The graph is obtained by taking Hollom's hypergraph and substituting the gadget $G_n$ with $n = 3 \cdot 401 + 1 = 1204$ for each of its six $3$-hyperedges, placing the gadget so that its apex $a$ is the transversal vertex; this yields $10 + 6 \cdot 1202 = 7{,}222$ vertices and $6 \cdot 2407 = 14{,}442$ edges. Three is the smallest number of transversal vertices for which the conjecture can fail.
--
--   The probability gap is tiny — the source estimates it at less than $10^{-4331}$ — so no computational search could have detected it; the argument is entirely structural.
--
--   **Formalization Note** ⚠️ The published Theorem 1.2 also asserts that $G$ is **planar**, and that assertion is omitted here: Mathlib has no notion of a planar graph, so the property cannot currently be stated. The formalized statement is therefore strictly weaker than the published one. Adding planarity would be a welcome strengthening. The vertex count is carried by the carrier type `Fin 7222`.
--
--   **Formalization Note (edge count).** The edge count is stated as `(ofEdges E).edgeFinset.card = 14442`, i.e. the number of edges of the *graph*, rather than the cardinality of the defining `Finset (Sym2 _)`. The two differ: `Sym2` contains diagonal pairs $\{x,x\}$, which `fromEdgeSet` silently discards, so constraining the raw `Finset` would have pinned the true edge count only to the range $[7221, 14442]$.
-- source:
--   N. Gladkov, I. Pak, A. Zimin, "The bunkbed conjecture is false", Proc. Natl. Acad. Sci. USA 122 (2025), no. 24, e2420725122, https://doi.org/10.1073/pnas.2420725122 - p. 1, Theorem 1.2; proof p. 7 (Section 4.2). Planarity omitted: absent from Mathlib.

import Definitions.Def_BunkbedHypergraph
open Bunkbed Bunkbed.Hyper SimpleGraph Finset

namespace BunkbedFalse

/-- **Theorem 1.2** (p. 1), with the planarity assertion omitted: Mathlib has no notion of a
planar graph. -/
theorem explicit_counterexample :
    ∃ (E : Finset (Sym2 (Fin 7222))) (T : Finset (Fin 7222)) (u v : Fin 7222),
      (ofEdges E).edgeFinset.card = 14442 ∧ T.card = 3 ∧ (ofEdges E).Connected ∧
      bbProb E (fun _ => (1 / 2 : ℚ)) T (u, 0) (v, 0)
        < bbProb E (fun _ => (1 / 2 : ℚ)) T (u, 0) (v, 1) := by sorry

end BunkbedFalse
