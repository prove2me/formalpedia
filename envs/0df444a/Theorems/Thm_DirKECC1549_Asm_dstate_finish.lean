-- Prove2me | Theorems.Thm_DirKECC1549_Asm_dstate_finish
-- name    : DirKECC1549.Asm.dstate_finish
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-16T06:12:03.794843+00:00
-- url     : https://prove2.me/theorems/92ba61f4-3aad-4960-9148-ec25efec891d
-- title:
--   Depth-first search: finishing a vertex
-- statement:
--   If all out-edges of the top vertex $v$ were scanned, popping $v$ and appending it to the post-order keeps `DState` (via `dfsH_finish`).
--
--   **Context.** This lemma belongs to the machine-checked word-RAM implementation of the strongly connected components computation used by Algorithm 3 (the child contract `scc_impl`): Kosaraju's algorithm with an iterative depth-first search on $D$ producing the post-order (pass 1), followed by searches on reversed edges from the vertices in decreasing post-order, each labelling one component (pass 2), all in $O(n+m)$ ticks on the graph layout.
-- source:
--   Loukas Georgiadis, Evangelos Kipouridis, Evangelos Kosinas, Charis Papadopoulos, Christos Pergaminelis, STOC 2027 submission #1549 (October 2026), Section 3.3, Algorithm 3 (p.17) and proof of Lemma 5 (pp.18–19); word-RAM model of Hagerup (p.25). Implementation-level lemma of the verified program for Lemma 5.

import Definitions.Def_DirKECC1549_Impl_SccDfs

set_option autoImplicit false
open Classical Finset
open DirKECC1549.Main DirKECC1549.Main.CostAux
open DirKECC1549 DirKECC1549.Asm
variable {n m : ℕ}

theorem DirKECC1549.Asm.dstate_finish (D : Fin m → Fin n × Fin n) (σ : Equiv.Perm (Fin m))
    (hσ : Monotone (fun i => ((D (σ i)).1 : ℕ))) (rest po : List (Fin n)) (v : Fin n)
    (ptr : Fin n → ℕ) (h : DState D σ (rest ++ [v]) po ptr) (hp : ots D (v + 1) ≤ ptr v) :
    DState D σ rest (po ++ [v]) ptr := by sorry
