-- Prove2me | Theorems.Thm_CutSetEnum_theorem_2_1
-- name    : CutSetEnum.theorem_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:15:18.760388+00:00
-- url     : https://prove2.me/theorems/29aa81a0-2f43-4b8f-af0b-80c1fbd02766
-- title:
--   Theorem 2.1 — some $S\subseteq U$, $|S|\le 2k-1$, recovers $\delta(U)$ against the sink $\bar U$
-- statement:
--   Let $G=(V,E)$ be a hypergraph and $k\ge2$ an integer, and let $(U,\bar U)$ be a 2-partition of $V$ with $d(U)=OPT_{k\text{-cut}}$. Then there is a non-empty set $S\subseteq U$ with
--   $$
--   |S|\le 2k-1
--   $$
--   such that every minimum $(S,\bar U)$-terminal cut $(A,\bar A)$ satisfies $\delta(A)=\delta(U)$.
--
--   This is the one-sided half of Theorem 1.4: the sink terminal set is all of $\bar U$. It already settles Theorem 1.4 when $|\bar U|\le 2k-1$.
--
--   Differences from the source:
--   - reading: “there exists a set S ⊆ U” → S ⊆ U and S non-empty; reason: (S, T)-terminal cuts are defined only for non-empty S (p.4); the stronger reading, and true: an empty witness can be replaced by any singleton {u} ⊆ U
--   - encoding: d(U) = OPT_k-cut (a minimum over k-partitions) → IsOptKCutValue H k (d H U): some k-partition has cost d(U) and none has less; reason: no sInf, so no junk value when V has fewer than k vertices; same instances
--   - encoding: (A, Ā) an (S, T)-terminal cut, a 2-partition with S ⊆ A ⊆ V \ T → published IsTerminalCut S T A := S ⊆ A ∧ Disjoint A T (no separate 2-partition clause); reason: for non-empty S and T the two coincide
--   - encoding: δ(A) = δ(U), equality of sets of hyperedges → cutSet H A = cutSet H U, equality of sub-multisets of the hyperedge multiset; reason: parallel copies of a hyperedge cross a cut together, so multiset and set equality agree
-- source:
--   Beideman, Chandrasekaran & Wang, Counting and enumerating optimum cut sets for hypergraph k-partitioning problems for fixed k, arXiv:2204.09178v2, Theorem 2.1, p.10 (PDF 11)

import Mathlib
import Definitions.Def_HyperKCut_Structure_Model
import Definitions.Def_CutSetEnum_cutSet
import Definitions.Def_CutSetEnum_IsOptKCutValue

open HyperKCut.Structure

namespace CutSetEnum

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **Theorem 2.1: a source set `S ⊆ U` with `|S| ≤ 2k − 1` recovers `δ(U)` against sink `Ū`.**
Beideman, Chandrasekaran & Wang, arXiv:2204.09178v2, Theorem 2.1, p.10 (PDF 11): "Let G = (V, E)
be a hypergraph and let OPT_k-cut be the optimum value of Hypergraph-k-Cut in G for some integer
k ≥ 2. Suppose (U, Ū) is a 2-partition of V with d(U) = OPT_k-cut. Then, there exists a set S ⊆ U
with |S| ≤ 2k − 1 such that every minimum (S, Ū)-terminal cut (A, Ā) satisfies δ(A) = δ(U)."

**Formalization Note.** `(U, Uᶜ)` is a 2-partition: `U` and `Uᶜ` non-empty. "d(U) = OPT_k-cut" is
`IsOptKCutValue H k (d H U)` (attained and least). The conclusion asserts `S` non-empty, because
the paper defines `(S, T)`-terminal cuts only for non-empty `S` and `T`. Terminal cuts are the
published `IsMinTerminalCut` (no separate 2-partition clause; equivalent for non-empty terminal
sets). The conclusion quantifies over **every** minimum `(S, Uᶜ)`-terminal cut and compares
cut-sets (`cutSet`, multiset equality), not cut values. -/
theorem theorem_2_1
    (H : HyperKCut.Structure.Hypergraph V) (k : ℕ) (hk : 2 ≤ k)
    (U : Finset V) (hU : U.Nonempty) (hUc : Uᶜ.Nonempty)
    (hopt : IsOptKCutValue H k (d H U)) :
    ∃ S : Finset V, S ⊆ U ∧ S.Nonempty ∧ S.card ≤ 2 * k - 1 ∧
      ∀ A : Finset V, IsMinTerminalCut H S Uᶜ A → cutSet H A = cutSet H U := by sorry

end CutSetEnum
