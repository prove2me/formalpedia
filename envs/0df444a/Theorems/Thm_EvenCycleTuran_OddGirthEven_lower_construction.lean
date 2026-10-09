-- Prove2me | Theorems.Thm_EvenCycleTuran_OddGirthEven_lower_construction
-- name    : EvenCycleTuran.OddGirthEven.lower_construction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:26:05.171007+00:00
-- url     : https://prove2.me/theorems/21ffc582-4db3-463f-a98c-f4f23f0475cd
-- title:
--   §6.2 — replacing high-girth hyperedges by odd cycles
-- statement:
--   Fix integers $k>l\ge2$. Let $\mathcal H$ be a $(2l+1)$-uniform hypergraph of Berge girth at least $2k+1$. Choose a cyclic order on every hyperedge and replace it by a copy of $C_{2l+1}$, obtaining a simple graph $G$. Then $G$ has no cycle of length between $3$ and $2k$ except possibly $2l+1$, and
--
--   $$\mathcal N(C_{2l+1},G)\ge |E(\mathcal H)|.$$
--
--   The construction turns the high-girth hypergraphs of Theorem 29 into the graph lower bound.
--
--   **Formalization Note** Every chosen order is an injective enumeration of exactly one hyperedge. The theorem holds for any such choices; no order is presupposed for an empty hypergraph.
-- source:
--   Gerbner, Győri, Methuku and Vizer, Generalized Turán problems for even cycles, arXiv:1712.07079v3, p. 27, §6.2, lower-bound paragraph of Theorem 17

import Mathlib
import Definitions.Def_EvenCycleTuran_OddGirthEven_Setting

namespace EvenCycleTuran.OddGirthEven

/-- The lower-bound construction in the proof of Theorem 17, p. 27. -/
theorem lower_construction (k l : ℕ) (hl : 2 ≤ l) (hkl : l < k)
    (n : ℕ) (H : Hypergraph (Fin n))
    (huniform : IsUniform H (2 * l + 1)) (hgirth : GirthGe H (2 * k + 1))
    (σ : (e : {e // e ∈ H}) → Fin (2 * l + 1) ↪ Fin n)
    (hσ : ∀ e, Finset.univ.map (σ e) = e.val) :
    EvenCycleTuran.C4Count.CycleFree (Set.Icc 3 (2 * k) \ {2 * l + 1})
      (replaceEdges H (2 * l + 1) σ) ∧
    H.card ≤ (replaceEdges H (2 * l + 1) σ).copyCount
      (SimpleGraph.cycleGraph (2 * l + 1)) := by sorry

end EvenCycleTuran.OddGirthEven
