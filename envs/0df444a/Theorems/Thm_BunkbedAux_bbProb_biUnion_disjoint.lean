-- Prove2me | Theorems.Thm_BunkbedAux_bbProb_biUnion_disjoint
-- name    : BunkbedAux.bbProb_biUnion_disjoint
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-12T04:13:52.880556+00:00
-- url     : https://prove2.me/theorems/8e553437-46c3-46c2-9a0b-af807db09ccf
-- title:
--   Bunkbed percolation factorises over edge-disjoint parts
-- statement:
--   In bunkbed percolation the two levels are percolated independently on the same edge set, so $\texttt{bbProb}$ is a double sum over pairs of configurations. If that edge set is a disjoint union $\bigcup_i E_i$, then each of the two configurations further factorises across the parts.
--
--   This theorem records the resulting fourfold-indexed form: for a pairwise disjoint family $E_i$ and any weight function $w$,
--
--   $$\mathbb{P}^{\mathrm{bb}}\bigl[x \leftrightarrow y\bigr] \;=\; \sum_{(S^0_i)} \sum_{(S^1_i)} \mathbf{1}\Bigl[x \leftrightarrow y \text{ in } \mathrm{BB}\Bigl(T, \bigcup_i S^0_i, \bigcup_i S^1_i\Bigr)\Bigr] \prod_i \mathrm{wt}_{E_i}(S^0_i) \prod_i \mathrm{wt}_{E_i}(S^1_i),$$
--
--   both sums running over tuples with $S^l_i \subseteq E_i$.
--
--   No hypothesis on $w$ is required: this is an algebraic rearrangement, obtained by applying the single-level factorisation once in each summation variable. The underlying facts are that configurations on a disjoint union correspond to tuples of configurations on the parts, and that the configuration weight factorises as a product of per-part weights.
--
--   **Mathematical role.** This is what makes a substituted graph tractable. If a graph is built by replacing each hyperedge of a hypergraph with a gadget copy, the copies are edge-disjoint, so this theorem presents bunkbed percolation on the whole graph as an independent choice of a configuration in each copy on each level. Combined with the fact that connectivity depends only on the partition each copy induces on its attachment vertices, it identifies the process with a Wierman--Ziff model on the hypergraph: one independent pair of states per hyperedge, one for each level.
-- source:
--   N. Gladkov, I. Pak, A. Zimin, The bunkbed conjecture is false, PNAS 122 (2025) no. 24, e2420725122, https://doi.org/10.1073/pnas.2420725122, Sections 3.2 and 4 (pp. 3, 6-7).

import Definitions.Def_BunkbedPercolation
open Bunkbed Finset SimpleGraph

namespace BunkbedAux

/-- **Bunkbed percolation factorises over edge-disjoint parts.** Both levels are percolated
independently, so for a pairwise disjoint family of edge sets the double sum defining `bbProb`
becomes a double sum over tuples of per-part configurations. -/
theorem bbProb_biUnion_disjoint {V : Type*} [Fintype V] [DecidableEq V]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : ι → Finset (Sym2 V)) (hdisj : ∀ i j, i ≠ j → Disjoint (E i) (E j))
    (w : Sym2 V → ℚ) (T : Finset V) (x y : V × Fin 2) :
    bbProb (Finset.univ.biUnion E) w T x y
      = ∑ S₀ ∈ Fintype.piFinset (fun i => (E i).powerset),
          ∑ S₁ ∈ Fintype.piFinset (fun i => (E i).powerset),
            (if (bbGraph T (Finset.univ.biUnion (fun i => S₀ i))
                  (Finset.univ.biUnion (fun i => S₁ i))).Reachable x y then (1 : ℚ) else 0)
              * (∏ i, weight (E i) w (S₀ i)) * (∏ i, weight (E i) w (S₁ i)) := by
  sorry

end BunkbedAux
