-- Prove2me | Theorems.Thm_ConantTerry_Orders_Supplement_lemma_4_3
-- name    : ConantTerry.Orders.Supplement.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T07:26:12.086598+00:00
-- url     : https://prove2.me/theorems/7d261a88-954b-4a7f-887a-0cbfcec1cd7b
-- title:
--   Lemma 4.3 — trees yield covered proto-ladders
-- statement:
--   Let $\mathcal I,\mathcal J$ be arbitrary finite covers of $[0,1]$, with $p=|\mathcal I|$ and $q=|\mathcal J|$. Let $X,Y$ be arbitrary sets and $f:X\times Y\to[0,1]$. For every integer $k\ge1$ and real $\delta>0$, put $t_k=\sum_{i=0}^{k-1}(pq)^i$. Then
--   $$
--   f\text{ admits a }(t_k,2\delta)\text{-tree}\quad\Longrightarrow\quad
--   f\text{ admits an }(\mathcal I,\mathcal J)\text{-covered }(k,\delta)\text{-proto-ladder}.
--   $$
--   Each cover consists of subsets whose union is the full unit interval. Members can be empty or overlap; they need not be intervals or form a partition. The exact height includes $p=q=1$, where it is $k$.
--
--   This supplies the covered intermediate configuration used in Theorem 1.14, with both coverage clauses and the row-dependent alternatives of Definition 4.1.
--
--   Differences from the source:
--   - encoding: arbitrary sets X,Y and values in [0,1] → arbitrary types X,Y and the real subtype Set.Icc 0 1; reason: the subtype enforces exactly the source range and adds no finiteness, nonemptiness or regularity assumption
--   - encoding: finite binary words and 1-based finite indices → published List Bool word subtypes and zero-based Fin indices; reason: length, prefix, orientation and index inequalities are preserved by relabeling
--   - encoding: finite collections of subsets covering [0,1] → Finset collections of subsets of the unit subtype, with explicit pointwise coverage; reason: cardinality is the number of distinct members, as in the source collections; no shape or disjointness restriction is added
-- source:
--   C. Terry, G. Conant, STOC 2027 submission #1299 (October 2026), p. 16, Lemma 4.3; proof pp. 16–18

import Mathlib
import Definitions.Def_ConantTerry_Orders_function_tree
import Definitions.Def_ConantTerry_Orders_Supplement_covered_proto_ladder
import Definitions.Def_ConantTerry_Orders_Supplement_extraction_heights

namespace ConantTerry.Orders.Supplement

/-- Lemma 4.3, pp.16-18. These finite covers can overlap and have empty
members; no interval or disjointness assumption is imposed. -/
theorem lemma_4_3 {X : Type*} {Y : Type*}
    (f : X × Y → Set.Icc (0 : ℝ) 1)
    (𝓘 𝓙 : Finset (Set (Set.Icc (0 : ℝ) 1)))
    (hI : ∀ z : Set.Icc (0 : ℝ) 1, ∃ I ∈ 𝓘, z ∈ I)
    (hJ : ∀ z : Set.Icc (0 : ℝ) 1, ∃ J ∈ 𝓙, z ∈ J)
    (k : ℕ) (hk : 1 ≤ k) (δ : ℝ) (hδ : 0 < δ)
    (htree : AdmitsTree f (protoHeight 𝓘.card 𝓙.card k) (2 * δ)) :
    AdmitsCoveredProtoLadder f k δ (↑𝓘) (↑𝓙) := by sorry

end ConantTerry.Orders.Supplement
