-- Prove2me | Theorems.Thm_CutSetEnum_theorem_1_4
-- name    : CutSetEnum.theorem_1_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:15:22.193624+00:00
-- url     : https://prove2.me/theorems/6ef6ea2d-1948-4b08-a9e6-d6a61cfc5577
-- title:
--   Theorem 1.4 — cut-sets of value $OPT_{k\text{-cut}}$ are recovered by every minimum $(S,T)$-terminal cut, $|S|,|T|\le 2k-1$
-- statement:
--   Let $G=(V,E)$ be a hypergraph (finite, unit costs, parallel hyperedges allowed) and let $k\ge2$ be an integer. Let $OPT_{k\text{-cut}}$ be the least number of hyperedges crossing a $k$-partition of $V$. Suppose $(U,\bar U)$ is a 2-partition of $V$ with
--   $$
--   d(U)=OPT_{k\text{-cut}} .
--   $$
--   Then there exist non-empty sets $S\subseteq U$ and $T\subseteq\bar U$ with
--   $$
--   |S|\le 2k-1\quad\text{and}\quad |T|\le 2k-1
--   $$
--   such that every minimum $(S,T)$-terminal cut $(A,\bar A)$ satisfies $\delta(A)=\delta(U)$.
--
--   This is the main structural theorem of the paper. Trying all pairs of terminal sets of size at most $2k-1$ and computing one minimum terminal cut for each yields a polynomial family, for fixed $k$, containing every cut-set of value $OPT_{k\text{-cut}}$; the paper's enumeration algorithms for min-$k$-cut-sets and minmax-$k$-cut-sets, and its polynomial bound on the number of minmax-$k$-cut-sets, are built on it. Only the cut-set, not the cut, can be recovered in general: a single hyperedge spanning $V$ makes every 2-partition optimal for $k=2$.
--
--   **Formalization Note** "$d(U)=OPT_{k\text{-cut}}$" is the predicate `IsOptKCutValue` (attained and least, no `sInf`). The conclusion quantifies over every minimum terminal cut and compares cut-sets, not cut values.
--
--   Differences from the source:
--   - reading: “there exist sets S ⊆ U, T ⊆ Ū” → S ⊆ U, T ⊆ Uᶜ, both non-empty; reason: (S, T)-terminal cuts are defined only for non-empty S, T (p.4); the stronger reading, and true: an empty witness can be replaced by a singleton on the same side
--   - encoding: d(U) = OPT_k-cut (a minimum over k-partitions) → IsOptKCutValue H k (d H U): some k-partition has cost d(U) and none has less; reason: no sInf, so no junk value when V has fewer than k vertices; same instances
--   - encoding: (A, Ā) an (S, T)-terminal cut, a 2-partition with S ⊆ A ⊆ V \ T → published IsTerminalCut S T A := S ⊆ A ∧ Disjoint A T (no separate 2-partition clause); reason: for non-empty S and T the two coincide
--   - encoding: δ(A) = δ(U), equality of sets of hyperedges → cutSet H A = cutSet H U, equality of sub-multisets of the hyperedge multiset; reason: parallel copies of a hyperedge cross a cut together, so multiset and set equality agree
-- source:
--   Beideman, Chandrasekaran & Wang, Counting and enumerating optimum cut sets for hypergraph k-partitioning problems for fixed k, arXiv:2204.09178v2, Theorem 1.4, p.5 (PDF 6), restated p.15 (PDF 16)

import Mathlib
import Definitions.Def_HyperKCut_Structure_Model
import Definitions.Def_CutSetEnum_cutSet
import Definitions.Def_CutSetEnum_IsOptKCutValue

open HyperKCut.Structure

namespace CutSetEnum

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **Theorem 1.4 (main structural theorem): cut-sets of value `OPT_k-cut` are recovered by every
minimum `(S, T)`-terminal cut for some `|S|, |T| ≤ 2k − 1`.**
Beideman, Chandrasekaran & Wang, *Counting and enumerating optimum cut sets for hypergraph
k-partitioning problems for fixed k*, arXiv:2204.09178v2, Theorem 1.4, p.5 (PDF 6), restated
p.15 (PDF 16): "Let G = (V, E) be a hypergraph and let OPT_k-cut be the optimum value of
Hypergraph-k-Cut in G for some integer k ≥ 2. Suppose (U, Ū) is a 2-partition of V with
d(U) = OPT_k-cut. Then, there exist sets S ⊆ U, T ⊆ Ū with |S| ≤ 2k − 1 and |T| ≤ 2k − 1 such
that every minimum (S, T)-terminal cut (A, Ā) satisfies δ(A) = δ(U)."

**Formalization Note.** The hypergraph is the published `HyperKCut.Structure.Hypergraph V`
(a multiset of vertex sets over a finite type `V`; unit costs, parallel hyperedges allowed).
`(U, Uᶜ)` is a 2-partition: `U` and `Uᶜ` non-empty. "d(U) = OPT_k-cut" is
`IsOptKCutValue H k (d H U)`: some k-partition crosses exactly `d(U)` hyperedges and none crosses
fewer (no `sInf`). The conclusion asserts `S` and `T` non-empty, because the paper defines
`(S, T)`-terminal cuts only for non-empty `S` and `T`; for such `S`, `T` the published
`IsMinTerminalCut` (which has no separate 2-partition clause) is the paper's notion. The
conclusion quantifies over **every** minimum `(S, T)`-terminal cut `(A, Aᶜ)` and asserts equality
of cut-sets `δ(A) = δ(U)` (`cutSet`, multiset equality), not only of cut values. -/
theorem theorem_1_4
    (H : HyperKCut.Structure.Hypergraph V) (k : ℕ) (hk : 2 ≤ k)
    (U : Finset V) (hU : U.Nonempty) (hUc : Uᶜ.Nonempty)
    (hopt : IsOptKCutValue H k (d H U)) :
    ∃ S T : Finset V, S ⊆ U ∧ T ⊆ Uᶜ ∧ S.Nonempty ∧ T.Nonempty ∧
      S.card ≤ 2 * k - 1 ∧ T.card ≤ 2 * k - 1 ∧
      ∀ A : Finset V, IsMinTerminalCut H S T A → cutSet H A = cutSet H U := by sorry

end CutSetEnum
