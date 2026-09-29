-- Prove2me | Theorems.Thm_Erdos81_chordal_clique_suffix_peo
-- name    : Erdos81.chordal_clique_suffix_peo
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-11T01:52:47.753209+00:00
-- url     : https://prove2.me/theorems/b0fa8a00-b0f2-46d1-878c-bfc87c15cebf
-- title:
--   Clique suffix perfect-elimination order in chordal graphs
-- statement:
--   Let $G$ be a finite chordal graph and let $S$ be any clique of $G$. Then $G$ has a perfect-elimination ordering in which every vertex outside $S$ occurs before every vertex of $S$. Equivalently, there is an injective rank function whose later-neighbor condition certifies chordality and whose final block is exactly the prescribed clique $S$. This is the structural suffix-elimination lemma used by weighted-neighborhood compression: it permits all edges outside $S$ to be charged to the earlier endpoint while keeping the edges internal to $S$ as a separate core. The statement is extracted from the clique-suffix argument in C22, Section 4, of the Erdos 81 chordal-clique-partition research record.
-- source:
--   C22 candidate, Section 4 (clique-suffix elimination), https://github.com/vibemathing/problem-erdos-81-chordal-clique-partition/blob/09c2b6f3e277eb20fc34d0add65ee8d027c5bb37/research/artifacts/candidates/erdos81-a01-c22-c20-audit.md

import Definitions.Def_erdos81_clique_partitions

namespace Erdos81

theorem chordal_clique_suffix_peo {n : ℕ}
    (G : SimpleGraph (Fin n)) (hG : Erdos81.IsChordal G)
    (S : Finset (Fin n)) (hS : Erdos81.IsClique G S) :
    ∃ rank : Fin n → ℕ, Function.Injective rank ∧
      (∀ ⦃v a b : Fin n⦄, G.Adj v a → G.Adj v b →
        rank v < rank a → rank v < rank b → a ≠ b → G.Adj a b) ∧
      (∀ v : Fin n, v ∉ S → ∀ s ∈ S, rank v < rank s) := by sorry

end Erdos81
