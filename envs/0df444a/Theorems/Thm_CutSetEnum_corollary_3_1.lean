-- Prove2me | Theorems.Thm_CutSetEnum_corollary_3_1
-- name    : CutSetEnum.corollary_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:15:22.125595+00:00
-- url     : https://prove2.me/theorems/d8bd47ee-a609-4f70-a001-942ee09e573f
-- title:
--   Corollary 3.1 — some $T\subseteq\bar U$, $|T|\le 2k-1$, recovers $\delta(U)$ against the source $U$
-- statement:
--   Let $G=(V,E)$ be a hypergraph and $k\ge2$ an integer, and let $(U,\bar U)$ be a 2-partition of $V$ with $d(U)=OPT_{k\text{-cut}}$. Then there is a non-empty set $T\subseteq\bar U$ with
--   $$
--   |T|\le 2k-1
--   $$
--   such that every minimum $(U,T)$-terminal cut $(A,\bar A)$ satisfies $\delta(A)=\delta(U)$.
--
--   This is Theorem 2.1 applied to the 2-partition $(\bar U,U)$, read back on the side of $U$.
--
--   Differences from the source:
--   - reading: “there exists a set T ⊆ Ū” → T ⊆ Uᶜ and T non-empty; reason: (S, T)-terminal cuts are defined only for non-empty T (p.4); the stronger reading, and true: an empty witness can be replaced by any singleton {v} ⊆ Ū
--   - encoding: d(U) = OPT_k-cut (a minimum over k-partitions) → IsOptKCutValue H k (d H U): some k-partition has cost d(U) and none has less; reason: no sInf, so no junk value when V has fewer than k vertices; same instances
--   - encoding: (A, Ā) an (S, T)-terminal cut, a 2-partition with S ⊆ A ⊆ V \ T → published IsTerminalCut S T A := S ⊆ A ∧ Disjoint A T (no separate 2-partition clause); reason: for non-empty S and T the two coincide
--   - encoding: δ(A) = δ(U), equality of sets of hyperedges → cutSet H A = cutSet H U, equality of sub-multisets of the hyperedge multiset; reason: parallel copies of a hyperedge cross a cut together, so multiset and set equality agree
-- source:
--   Beideman, Chandrasekaran & Wang, Counting and enumerating optimum cut sets for hypergraph k-partitioning problems for fixed k, arXiv:2204.09178v2, Corollary 3.1, p.15 (PDF 16)

import Mathlib
import Definitions.Def_HyperKCut_Structure_Model
import Definitions.Def_CutSetEnum_cutSet
import Definitions.Def_CutSetEnum_IsOptKCutValue

open HyperKCut.Structure

namespace CutSetEnum

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **Corollary 3.1: a sink set `T ⊆ Ū` with `|T| ≤ 2k − 1` recovers `δ(U)` against source `U`.**
Beideman, Chandrasekaran & Wang, arXiv:2204.09178v2, Corollary 3.1, p.15 (PDF 16): "Let
G = (V, E) be a hypergraph and let OPT_k-cut be the optimum value of Hypergraph-k-Cut in G for
some integer k ≥ 2. Suppose (U, Ū) is a 2-partition of V with d(U) = OPT_k-cut. Then, there
exists a set T ⊆ Ū with |T| ≤ 2k − 1 such that every minimum (U, T)-terminal cut (A, Ā) satisfies
δ(A) = δ(U)."

**Formalization Note.** `(U, Uᶜ)` is a 2-partition: `U` and `Uᶜ` non-empty. "d(U) = OPT_k-cut" is
`IsOptKCutValue H k (d H U)`. The conclusion asserts `T` non-empty, because the paper defines
`(S, T)`-terminal cuts only for non-empty `S` and `T`. The source terminal set is `U` itself; the
conclusion quantifies over **every** minimum `(U, T)`-terminal cut and compares cut-sets. -/
theorem corollary_3_1
    (H : HyperKCut.Structure.Hypergraph V) (k : ℕ) (hk : 2 ≤ k)
    (U : Finset V) (hU : U.Nonempty) (hUc : Uᶜ.Nonempty)
    (hopt : IsOptKCutValue H k (d H U)) :
    ∃ T : Finset V, T ⊆ Uᶜ ∧ T.Nonempty ∧ T.card ≤ 2 * k - 1 ∧
      ∀ A : Finset V, IsMinTerminalCut H U T A → cutSet H A = cutSet H U := by sorry

end CutSetEnum
