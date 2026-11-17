-- Prove2me | Theorems.Thm_DirKECC1549_Asm_bstate_edge
-- name    : DirKECC1549.Asm.bstate_edge
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-16T06:12:31.949833+00:00
-- url     : https://prove2.me/theorems/d13cad0b-34a7-4a6e-b652-ceab1dc0f24c
-- title:
--   Reverse search: scanning one in-edge
-- statement:
--   Scanning the in-edge at position $j$ of the current queue vertex either appends its tail (if new and outside $A$) or leaves the queue, and the scanned prefix of in-edges grows by one.
--
--   **Context.** This lemma belongs to the machine-checked word-RAM implementation of the strongly connected components computation used by Algorithm 3 (the child contract `scc_impl`): Kosaraju's algorithm with an iterative depth-first search on $D$ producing the post-order (pass 1), followed by searches on reversed edges from the vertices in decreasing post-order, each labelling one component (pass 2), all in $O(n+m)$ ticks on the graph layout.
-- source:
--   Loukas Georgiadis, Evangelos Kipouridis, Evangelos Kosinas, Charis Papadopoulos, Christos Pergaminelis, STOC 2027 submission #1549 (October 2026), Section 3.3, Algorithm 3 (p.17) and proof of Lemma 5 (pp.18–19); word-RAM model of Hagerup (p.25). Implementation-level lemma of the verified program for Lemma 5.

import Definitions.Def_DirKECC1549_Impl_SccBfs

set_option autoImplicit false
open Classical Finset
open DirKECC1549.Main DirKECC1549.Main.CostAux
open DirKECC1549 DirKECC1549.Asm
variable {n m : ℕ}

theorem DirKECC1549.Asm.bstate_edge (D : Fin m → Fin n × Fin n) (τ : Equiv.Perm (Fin m))
    (hτ : Monotone (fun i => ((D (τ i)).2 : ℕ))) (A : Finset (Fin n)) (v : Fin n)
    (q : List (Fin n)) (h : ℕ) (hB : BState D A v q h) (hh : h < q.length) (j : Fin m)
    (hj1 : its D (q[h]) ≤ j) (hj2 : (j : ℕ) < its D (q[h] + 1)) (hP : BPart D τ A q q[h] j) :
    let y := (D (τ j)).1
    (y ∉ A → y ∉ q → BState D A v (q ++ [y]) h ∧ BPart D τ A (q ++ [y]) q[h] (j + 1)) ∧
    (y ∈ A ∨ y ∈ q → BPart D τ A q q[h] (j + 1)) := by sorry
