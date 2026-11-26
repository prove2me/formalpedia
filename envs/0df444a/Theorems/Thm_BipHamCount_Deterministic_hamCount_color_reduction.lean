-- Prove2me | Theorems.Thm_BipHamCount_Deterministic_hamCount_color_reduction
-- name    : BipHamCount.Deterministic.hamCount_color_reduction
-- status  : Proved
-- author  : @Soh Kumabe
-- created : 2026-11-26T10:54:03.0138+00:00
-- url     : https://prove2.me/theorems/3672aba2-5ad8-54e2-9786-28dabebb6efc
-- title:
--   Theorem 1.1: reduction of a properly two-coloured digraph to the two adjacency matrices
-- statement:
--   Let $c$ be a proper two-colouring of a finite digraph on the ordered vertex set $[n]$. List the vertices of each colour in increasing order. If the lists have unequal length, there are no directed Hamiltonian cycles. If both have length $m$, form the $m$ by $m$ zero–one adjacency matrices for the arcs in each direction between the lists. The number of directed Hamiltonian cycles of the original digraph equals the number in the bipartite digraph encoded by these two matrices.
-- source:
--   Koana, Kumabe, Counting Hamiltonian Cycles in Bipartite Digraphs Deterministically in O(1.9526^n) Time, STOC 2027 submission #814 (October 2026), Lemma 4.4, p. 8. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/814.pdf

import Mathlib
import Definitions.Def_BipHamCount_Deterministic_Core

namespace BipHamCount.Deterministic

theorem hamCount_color_reduction (n : ℕ) (g : Fin n → Fin n → Bool) (c : Fin n → Bool)
    (hc : ∀ i j, g i j=true → c i≠c j) :
    let L := (List.finRange n).filter (fun i => decide (c i=false))
    let R := (List.finRange n).filter (fun i => decide (c i=true))
    if h : L.length=R.length then
      let f := L.get
      let t := fun i : Fin L.length => R.get (Fin.cast h i)
      let A : Matrix (Fin L.length) (Fin L.length) ℤ := fun i j => if g (f i) (t j) then 1 else 0
      let B : Matrix (Fin L.length) (Fin L.length) ℤ := fun j i => if g (t j) (f i) then 1 else 0
      hamCount g=hamCount (bipDigraph A B)
    else hamCount g=0 := by sorry

end BipHamCount.Deterministic
