-- Prove2me | Theorems.Thm_CutSetEnum_proposition_2_1
-- name    : CutSetEnum.proposition_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:16:41.613204+00:00
-- url     : https://prove2.me/theorems/6fd5e57e-505e-4df7-b13f-b667728440b2
-- title:
--   Proposition 2.1 — every minimum $(S,\bar U)$-terminal cut has cut-set $\delta(U)$
-- statement:
--   Let $G=(V,E)$ be a hypergraph, $k\ge2$, and $(U,\bar U)$ a 2-partition of $V$ with $d(U)=OPT_{k\text{-cut}}$. Let
--   $$
--   \mathcal C=\{Q\subseteq V:\ \bar U\subsetneq Q,\ d(Q)\le d(U),\ \delta(Q)\ne\delta(U)\}
--   $$
--   and let $S$ be a non-empty, inclusion-wise minimal subset of $U$ that meets every member of $\mathcal C$. Then every minimum $(S,\bar U)$-terminal cut $(A,\bar A)$ satisfies
--   $$
--   \delta(A)=\delta(U).
--   $$
--
--   Together with Lemma 2.1 (which bounds $|S|$ by $2k-1$) this proves Theorem 2.1.
--
--   **Formalization Note** $S$ is assumed non-empty because the paper defines $(S,T)$-terminal cuts only for non-empty terminal sets.
--
--   Differences from the source:
--   - encoding: S a minimal transversal of 𝒞 (non-emptiness implicit in “(S, Ū)-terminal cut”) → hypothesis S.Nonempty; reason: (S, T)-terminal cuts are defined only for non-empty S (p.4); excludes only the undefined case
--   - encoding: d(U) = OPT_k-cut (a minimum over k-partitions) → IsOptKCutValue H k (d H U): some k-partition has cost d(U) and none has less; reason: no sInf, so no junk value when V has fewer than k vertices; same instances
--   - encoding: (A, Ā) an (S, T)-terminal cut, a 2-partition with S ⊆ A ⊆ V \ T → published IsTerminalCut S T A := S ⊆ A ∧ Disjoint A T (no separate 2-partition clause); reason: for non-empty S and T the two coincide
--   - encoding: δ(A) = δ(U), equality of sets of hyperedges → cutSet H A = cutSet H U, equality of sub-multisets of the hyperedge multiset; reason: parallel copies of a hyperedge cross a cut together, so multiset and set equality agree
-- source:
--   Beideman, Chandrasekaran & Wang, Counting and enumerating optimum cut sets for hypergraph k-partitioning problems for fixed k, arXiv:2204.09178v2, Proposition 2.1, p.11 (PDF 12); setting from Theorem 2.1, proof, p.10 (PDF 11)

import Mathlib
import Definitions.Def_HyperKCut_Structure_Model
import Definitions.Def_CutSetEnum_cutSet
import Definitions.Def_CutSetEnum_IsOptKCutValue
import Definitions.Def_CutSetEnum_Coll
import Definitions.Def_CutSetEnum_IsMinTransversal

open HyperKCut.Structure

namespace CutSetEnum

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **Proposition 2.1: every minimum `(S, Ū)`-terminal cut has cut-set `δ(U)`.**
Beideman, Chandrasekaran & Wang, arXiv:2204.09178v2, Proposition 2.1, p.11 (PDF 12), in the
setting of the proof of Theorem 2.1, p.10 (PDF 11): "Let G = (V, E) be a hypergraph and let
OPT_k-cut be the optimum value of Hypergraph-k-Cut in G for some integer k ≥ 2. Suppose (U, Ū) is
a 2-partition of V with d(U) = OPT_k-cut. … Let S be an inclusion-wise minimal subset of U such
that S ∩ Q ≠ ∅ for all Q ∈ C … Proposition 2.1. Every minimum (S, Ū)-terminal cut (A, Ā) has
δ(A) = δ(U)."

**Formalization Note.** `(U, Uᶜ)` is a 2-partition: `U` and `Uᶜ` non-empty. "d(U) = OPT_k-cut" is
`IsOptKCutValue H k (d H U)`. `S` is a minimal transversal of `C` inside `U`
(`IsMinTransversal`). `S` is assumed non-empty because the paper defines `(S, T)`-terminal cuts
only for non-empty `S` and `T`. Cut-sets are compared as multisets (`cutSet`). -/
theorem proposition_2_1
    (H : HyperKCut.Structure.Hypergraph V) (k : ℕ) (hk : 2 ≤ k)
    (U : Finset V) (hU : U.Nonempty) (hUc : Uᶜ.Nonempty)
    (hopt : IsOptKCutValue H k (d H U))
    (S : Finset V) (hS : IsMinTransversal H U S) (hSne : S.Nonempty) :
    ∀ A : Finset V, IsMinTerminalCut H S Uᶜ A → cutSet H A = cutSet H U := by sorry

end CutSetEnum
