-- Prove2me | Theorems.Thm_BunkbedAux_wzEdges_reach_iff
-- name    : BunkbedAux.wzEdges_reach_iff
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-12T04:13:50.948204+00:00
-- url     : https://prove2.me/theorems/d303aad3-362f-4f7e-99f6-8793bb16081f
-- title:
--   A Wierman--Ziff state realises exactly its own partition
-- statement:
--   In the Wierman--Ziff model a hyperedge in state $s$ contributes, on a given level, a canonical set of edges among its three vertices: all three pairs for $abc$, a single pair for each of $ab|c$, $ac|b$, $a|bc$, and nothing for $a|b|c$.
--
--   For the model to mean what its notation says, one needs that these canonical edge sets realise **exactly** the named partition — that they join the pairs the state advertises and, crucially, *no others*. This theorem is that statement. For distinct $a, b, c$ and any level $l$,
--
--   $$(a,l) \leftrightarrow (b,l) \iff s \in \{abc,\ ab|c\}, \qquad (b,l) \leftrightarrow (c,l) \iff s \in \{abc,\ a|bc\}, \qquad (a,l) \leftrightarrow (c,l) \iff s \in \{abc,\ ac|b\},$$
--
--   connectivity being taken in the graph whose only edges are the canonical ones for $s$.
--
--   The forward implications are the substantive half: one must rule out connections arising through a path rather than a single edge. With at most three edges on three vertices and the endpoints distinct, this comes down to showing no other vertex is available as an intermediate — which is where the distinctness hypotheses are used.
--
--   **Mathematical role.** This is the bridge between a hyperedge gadget and the state it is supposed to simulate. A gadget copy's percolation configuration induces some partition of its three attachment vertices, and the five partition probabilities are the probabilities of the five possible patterns. To replace the gadget by an abstract Wierman--Ziff state one needs to know that the state's canonical edges induce the *same* partition — otherwise the substitution would change connectivity. Together with the fact that connectivity across edge-disjoint parts depends only on the boundary partitions, this yields the identification of bunkbed percolation on a substituted graph with a Wierman--Ziff model on the underlying hypergraph.
-- source:
--   N. Gladkov, I. Pak, A. Zimin, The bunkbed conjecture is false, PNAS 122 (2025) no. 24, e2420725122, https://doi.org/10.1073/pnas.2420725122, Sections 3.2 and 4 (pp. 3, 6-7).

import Definitions.Def_BunkbedHypergraph
open Bunkbed Bunkbed.Hyper Finset SimpleGraph

namespace BunkbedAux

/-- **A Wierman-Ziff state realises exactly its own partition.** The canonical edge set that a
state contributes inside one hyperedge on one level joins precisely the pairs the state names, and
no others. -/
theorem wzEdges_reach_iff {V : Type*} [Fintype V] [DecidableEq V] (a b c : V)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (l : Fin 2) (s : WZ) :
    ((ofEdges (WZ.edges s (a, b, c) l)).Reachable (a, l) (b, l) ↔ (s = WZ.abc ∨ s = WZ.ab_c))
    ∧ ((ofEdges (WZ.edges s (a, b, c) l)).Reachable (b, l) (c, l) ↔ (s = WZ.abc ∨ s = WZ.a_bc))
    ∧ ((ofEdges (WZ.edges s (a, b, c) l)).Reachable (a, l) (c, l) ↔ (s = WZ.abc ∨ s = WZ.ac_b)) := by
  sorry

end BunkbedAux
