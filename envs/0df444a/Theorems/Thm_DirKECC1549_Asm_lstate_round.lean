-- Prove2me | Theorems.Thm_DirKECC1549_Asm_lstate_round
-- name    : DirKECC1549.Asm.lstate_round
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-16T06:12:12.775373+00:00
-- url     : https://prove2.me/theorems/1d36d4ea-b297-4b5a-a34f-84e3253ea7c8
-- title:
--   Labelling one component
-- statement:
--   If the labels of $A$ form a valid partial labelling with $c$ classes and $v\notin A$, labelling the component of $v$ with $c$ gives a valid partial labelling of $A\cup\mathrm{SCC}(v)$ with $c+1$ classes.
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

theorem DirKECC1549.Asm.lstate_round (D : Fin m → Fin n × Fin n) (A : Finset (Fin n)) (lab lab' : Fin n → ℕ) (c : ℕ)
    (hL : LState D A lab c) (v : Fin n) (hv : v ∉ A)
    (hlab : ∀ u, lab' u = if StronglyConn D v u then c else lab u) :
    LState D (A ∪ univ.filter (fun u => StronglyConn D v u)) lab' (c + 1) := by sorry
