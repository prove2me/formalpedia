-- Prove2me | Theorems.Thm_BunkbedFalse_bb_boundary_reduce
-- name    : BunkbedFalse.bb_boundary_reduce
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-12T04:57:56.796837+00:00
-- url     : https://prove2.me/theorems/5836ba26-1e39-41fd-b0c6-de053eecf8ce
-- title:
--   Bunkbed reachability depends only on the per-copy boundary partitions
-- statement:
--   This is the geometric heart of the gadget substitution: it says that the $7{,}222$-vertex substituted graph and the $10$-vertex Wierman--Ziff graph have *the same* bunkbed connectivity between hypergraph vertices, provided each gadget copy realises the partition its state prescribes.
--
--   Let $S^0_i$ and $S^1_i$ be the open edges of copy $i$ on levels $0$ and $1$, and let $\psi$ assign a Wierman--Ziff state to each (hyperedge, level) pair. Assume the **matching hypothesis**: for every copy $i$ and level $l$, the three attachment vertices of copy $i$ are joined by the open edges of that copy at that level exactly as $\psi(i,l)$ says — the apex to the first path end iff $\psi(i,l) \in \{abc, ab|c\}$, the two path ends to each other iff $\psi(i,l) \in \{abc, a|bc\}$, and the apex to the second path end iff $\psi(i,l) \in \{abc, ac|b\}$. Then for all hypergraph vertices $x, y$ and every level $l$,
--   $$(x,0) \leftrightarrow (y,l) \text{ in the bunkbed over the substituted graph} \iff (x,0) \leftrightarrow (y,l) \text{ in the Wierman--Ziff bunkbed}.$$
--
--   Why it holds: both graphs are unions of parts meeting only along the lifted hypergraph vertices — on one side the six copies at each level plus the posts, on the other the canonical state edge sets plus the posts. A copy's interior vertices are private to it, and the canonical edge sets have no interior vertices at all. So connectivity between boundary vertices depends only on what each part does to the boundary, and the matching hypothesis says the corresponding parts do the same thing.
--
--   Note the hypothesis is satisfiable and the statement is not vacuous: with every gadget edge closed, each copy realises the state $a|b|c$ on both levels.
--
--   **Mathematical role.** This is what collapses the substituted graph's enormous configuration space onto the hypergraph. Combined with the factorisation of percolation across the edge-disjoint copies and the identification of each copy's partition probabilities with the gadget's, it shows that bunkbed percolation on the counterexample graph *is* a Wierman--Ziff model on Hollom's hypergraph — which is what allows the robustness lemma to transfer Hollom's hypergraph counterexample to an honest graph.
-- source:
--   N. Gladkov, I. Pak, A. Zimin, The bunkbed conjecture is false, PNAS 122 (2025) no. 24, e2420725122, https://doi.org/10.1073/pnas.2420725122, Section 4 (pp. 6-7), gadget substitution.

import Definitions.Def_BunkbedSubstituted
open Bunkbed Bunkbed.Hyper Finset SimpleGraph

namespace BunkbedFalse

/-- **Bunkbed reachability depends only on the per-copy boundary partitions.** If, for every copy
and every level, the open edges of that copy connect its three attachment vertices exactly as the
Wierman-Ziff state prescribes, then reachability between lifted hypergraph vertices in the bunkbed
graph over the substituted graph agrees with reachability in the Wierman-Ziff graph. -/
theorem bb_boundary_reduce (S₀ S₁ : Fin 6 → Finset (Sym2 (Fin 7222)))
    (hsub : ∀ i, S₀ i ⊆ (gadgetE 1204).image (Sym2.map (Bunkbed.Sub.emb i)))
    (hsub' : ∀ i, S₁ i ⊆ (gadgetE 1204).image (Sym2.map (Bunkbed.Sub.emb i)))
    (ψ : Fin 6 × Fin 2 → WZ)
    (hmatch : ∀ (i : Fin 6) (l : Fin 2),
        ((ofEdges (if l = 0 then S₀ i else S₁ i)).Reachable
              (Bunkbed.Sub.emb i 0) (Bunkbed.Sub.emb i 1)
            ↔ (ψ (i, l) = WZ.abc ∨ ψ (i, l) = WZ.ab_c))
      ∧ ((ofEdges (if l = 0 then S₀ i else S₁ i)).Reachable
              (Bunkbed.Sub.emb i 1) (Bunkbed.Sub.emb i 1204)
            ↔ (ψ (i, l) = WZ.abc ∨ ψ (i, l) = WZ.a_bc))
      ∧ ((ofEdges (if l = 0 then S₀ i else S₁ i)).Reachable
              (Bunkbed.Sub.emb i 0) (Bunkbed.Sub.emb i 1204)
            ↔ (ψ (i, l) = WZ.abc ∨ ψ (i, l) = WZ.ac_b)))
    (x y : Fin 10) (l : Fin 2) :
    (bbGraph Bunkbed.Sub.subT (Finset.univ.biUnion S₀) (Finset.univ.biUnion S₁)).Reachable
        (Bunkbed.Sub.iota x, 0) (Bunkbed.Sub.iota y, l)
      ↔ (wzGraph hollomTriple hollomT ψ).Reachable (x, 0) (y, l) := by
  sorry

end BunkbedFalse
