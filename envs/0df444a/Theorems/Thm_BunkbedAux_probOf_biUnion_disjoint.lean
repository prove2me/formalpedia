-- Prove2me | Theorems.Thm_BunkbedAux_probOf_biUnion_disjoint
-- name    : BunkbedAux.probOf_biUnion_disjoint
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-12T03:55:55.020912+00:00
-- url     : https://prove2.me/theorems/bda1b4aa-c53c-4454-a1e1-3a719dd938fe
-- title:
--   Percolation is independent across edge-disjoint parts
-- statement:
--   Bernoulli bond percolation retains each edge independently, so percolation on a disjoint union of edge sets ought to be the product of the percolations on the pieces. This theorem is that statement, in the combinatorial form in which percolation is defined here.
--
--   Let $E_i$, for $i$ in a finite index type, be **pairwise disjoint** finite sets of edges, and let $w$ be an arbitrary weight function. For any decidable event $\mathcal{E}$ on configurations,
--
--   $$\mathbb{P}_{\bigcup_i E_i}\bigl[\mathcal{E}\bigr] \;=\; \sum_{(S_i)} \Bigl(\prod_i \mathrm{wt}_{E_i}(S_i)\Bigr)\, \mathbf{1}\Bigl[\mathcal{E}\Bigl(\bigcup_i S_i\Bigr)\Bigr],$$
--
--   the sum running over all tuples with $S_i \subseteq E_i$.
--
--   The content is twofold. Configurations on the union correspond bijectively to tuples of configurations on the parts, via $S \mapsto (S \cap E_i)_i$ and $(S_i)_i \mapsto \bigcup_i S_i$ — and it is disjointness that makes this a bijection. And the configuration weight factors, $\mathrm{wt}_{\bigcup E_i}\bigl(\bigcup S_i\bigr) = \prod_i \mathrm{wt}_{E_i}(S_i)$, because both the product over retained edges and the product over deleted edges split along the partition.
--
--   Note that no hypothesis on $w$ is needed: the identity is an algebraic rearrangement, not a probabilistic argument, and holds for arbitrary weights.
--
--   **Mathematical role.** This is the first of the two ingredients needed to analyse a graph built by substituting a gadget for each hyperedge of a hypergraph. The gadget copies are edge-disjoint, so this theorem reduces percolation on the substituted graph to independent percolation within each copy — which is exactly what makes the induced process on the hypergraph a product of per-hyperedge states, i.e. a Wierman--Ziff model. The second ingredient is that connectivity across the union depends only on what each part does to the vertices it shares with the others.
-- source:
--   N. Gladkov, I. Pak, A. Zimin, The bunkbed conjecture is false, PNAS 122 (2025) no. 24, e2420725122, https://doi.org/10.1073/pnas.2420725122, Section 4 (pp. 6-7), where a gadget graph is substituted for each hyperedge.

import Definitions.Def_BunkbedPercolation
open Bunkbed Finset

namespace BunkbedAux

/-- **Independence across edge-disjoint parts.** If a family of edge sets is pairwise disjoint,
Bernoulli bond percolation on their union is the product of the percolations on the parts: the
probability of any event is a sum over tuples of per-part configurations, weighted by the product
of the per-part weights. -/
theorem probOf_biUnion_disjoint {V : Type*} [Fintype V] [DecidableEq V]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (E : ι → Finset (Sym2 V))
    (hdisj : ∀ i j, i ≠ j → Disjoint (E i) (E j))
    (w : Sym2 V → ℚ) (ev : Finset (Sym2 V) → Prop) [DecidablePred ev] :
    probOf (Finset.univ.biUnion E) w ev
      = ∑ S ∈ Fintype.piFinset (fun i => (E i).powerset),
          (∏ i, weight (E i) w (S i)) *
            (if ev (Finset.univ.biUnion (fun i => S i)) then (1 : ℚ) else 0) := by
  sorry

end BunkbedAux
