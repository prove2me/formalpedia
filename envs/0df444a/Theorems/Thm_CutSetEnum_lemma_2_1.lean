-- Prove2me | Theorems.Thm_CutSetEnum_lemma_2_1
-- name    : CutSetEnum.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:17:16.193981+00:00
-- url     : https://prove2.me/theorems/458beb59-a26f-4d73-ad40-dfba23977f64
-- title:
--   Lemma 2.1 — a minimal transversal of $\mathcal C$ has at most $2k-1$ vertices
-- statement:
--   Let $G=(V,E)$ be a hypergraph, $k\ge2$, and $(U,\bar U)$ a 2-partition of $V$ with $d(U)=OPT_{k\text{-cut}}$. Let
--   $$
--   \mathcal C=\{Q\subseteq V:\ \bar U\subsetneq Q,\ d(Q)\le d(U),\ \delta(Q)\ne\delta(U)\},
--   $$
--   and let $S$ be an inclusion-wise minimal subset of $U$ that meets every member of $\mathcal C$. Then
--   $$
--   |S|\le 2k-1 .
--   $$
--
--   With Proposition 2.1 this gives Theorem 2.1. The proof is by contradiction through Claims 2.1–2.6 and the strict conclusion of Theorem 1.5.
--
--   Differences from the source:
--   - encoding: d(U) = OPT_k-cut (a minimum over k-partitions) → IsOptKCutValue H k (d H U): some k-partition has cost d(U) and none has less; reason: no sInf, so no junk value when V has fewer than k vertices; same instances
-- source:
--   Beideman, Chandrasekaran & Wang, Counting and enumerating optimum cut sets for hypergraph k-partitioning problems for fixed k, arXiv:2204.09178v2, Lemma 2.1, p.11 (PDF 12); setting from Theorem 2.1, proof, p.10 (PDF 11)

import Mathlib
import Definitions.Def_HyperKCut_Structure_Model
import Definitions.Def_CutSetEnum_IsOptKCutValue
import Definitions.Def_CutSetEnum_Coll
import Definitions.Def_CutSetEnum_IsMinTransversal

open HyperKCut.Structure

namespace CutSetEnum

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **Lemma 2.1: a minimal transversal of `C` has at most `2k − 1` vertices.**
Beideman, Chandrasekaran & Wang, arXiv:2204.09178v2, Lemma 2.1, p.11 (PDF 12), in the setting of
the proof of Theorem 2.1, p.10 (PDF 11): "Let G = (V, E) be a hypergraph and let OPT_k-cut be the
optimum value of Hypergraph-k-Cut in G for some integer k ≥ 2. Suppose (U, Ū) is a 2-partition of
V with d(U) = OPT_k-cut. … Consider the collection C := {Q ⊆ V : Ū ⊊ Q, d(Q) ≤ d(U), and
δ(Q) ≠ δ(U)}. Let S be an inclusion-wise minimal subset of U such that S ∩ Q ≠ ∅ for all Q ∈ C …
Lemma 2.1. The size of the subset S is at most 2k − 1."

**Formalization Note.** `(U, Uᶜ)` is a 2-partition: `U` and `Uᶜ` non-empty. "d(U) = OPT_k-cut" is
`IsOptKCutValue H k (d H U)`. `S` is any minimal transversal of `C = Coll H U` inside `U`
(`IsMinTransversal`); the statement holds for every such `S`. `2 * k - 1` is natural-number
subtraction, harmless since `k ≥ 2`. -/
theorem lemma_2_1
    (H : HyperKCut.Structure.Hypergraph V) (k : ℕ) (hk : 2 ≤ k)
    (U : Finset V) (hU : U.Nonempty) (hUc : Uᶜ.Nonempty)
    (hopt : IsOptKCutValue H k (d H U))
    (S : Finset V) (hS : IsMinTransversal H U S) :
    S.card ≤ 2 * k - 1 := by sorry

end CutSetEnum
