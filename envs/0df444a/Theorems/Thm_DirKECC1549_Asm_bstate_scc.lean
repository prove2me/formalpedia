-- Prove2me | Theorems.Thm_DirKECC1549_Asm_bstate_scc
-- name    : DirKECC1549.Asm.bstate_scc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-16T06:12:23.837194+00:00
-- url     : https://prove2.me/theorems/df3f7dd9-1480-4298-85d2-1495dac47df1
-- title:
--   Reverse search: a completed search is the component
-- statement:
--   For a vertex $v$ of maximal post-order position outside the labelled set $A$ (closed under strong connectivity), a completed reverse search from $v$ avoiding $A$ visits exactly the vertices strongly connected to $v$ (by `kosaraju_key`).
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

theorem DirKECC1549.Asm.bstate_scc (D : Fin m → Fin n × Fin n) (pos : Fin n → ℕ) (hpos : Function.Injective pos)
    (hKP : KP D pos) (A : Finset (Fin n)) (hA : ∀ a b, StronglyConn D a b → a ∈ A → b ∈ A)
    (v : Fin n) (hvA : v ∉ A) (hmax : ∀ x, x ∉ A → pos x ≤ pos v) (q : List (Fin n))
    (hB : BState D A v q q.length) : ∀ u, u ∈ q ↔ StronglyConn D v u := by sorry
