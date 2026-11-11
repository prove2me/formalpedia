-- Prove2me | Theorems.Thm_DigraphDFSStream_Main_lemma_4_4
-- name    : DigraphDFSStream.Main.lemma_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:21:03.944678+00:00
-- url     : https://prove2.me/theorems/6aaa01a6-0ef3-435d-beb1-46d09fca9218
-- title:
--   Lemma 4.4 — a separation dichotomy
-- statement:
--   Let $G=([n],E)$ be a directed graph, with $n\ge2$ as in §4, and let $U,A,B\subseteq[n]$ be pairwise disjoint. Suppose that every SCC of $G[U]$ has at most $n/2$ vertices and there is no directed path from $A$ to $B$ in $G[U\cup A\cup B]$. Then
--   $$\operatorname{sccmax}(G[U\cup A])\le n/2\quad\text{or}\quad\operatorname{sccmax}(G[U\cup B])\le n/2.$$
--   The threshold remains the size of the ambient graph divided by two in both alternatives. This is the dichotomy used by the separator path-count reduction.
--
--   Differences from the source:
--   - encoding: induced subgraphs on pairwise disjoint vertex sets and the threshold n/2 → finite vertex subsets of Fin n and the comparisons 2 * sccmax ≤ n; reason: these comparisons are exactly the real half-size threshold, without rounding; n ≥ 2 is the standing convention of §4
-- source:
--   Prantar Ghosh, Amirhossein Janfaza, STOC 2027 submission #1648 (October 2026), Lemma 4.4, printed p.13 (PDF p.14)

import Definitions.Def_DigraphDFSStream_Main_GraphSemantics

set_option autoImplicit false

namespace DigraphDFSStream.Main

/-- Ghosh--Janfaza, STOC 2027 submission #1648, Lemma 4.4, printed p.13 (PDF p.14).
The comparison uses the fixed ambient n, including for the three induced subgraphs. -/
theorem lemma_4_4 {n : ℕ} (hn : 2 ≤ n) (E : Finset (Fin n × Fin n))
    (U A B : Finset (Fin n)) (hUA : Disjoint U A) (hUB : Disjoint U B)
    (hAB : Disjoint A B) (hU : 2 * sccmax E U ≤ n)
    (hNoPath : ∀ a ∈ A, ∀ b ∈ B, ¬ Reach E (U ∪ A ∪ B) a b) :
    2 * sccmax E (U ∪ A) ≤ n ∨ 2 * sccmax E (U ∪ B) ≤ n := by sorry

end DigraphDFSStream.Main
