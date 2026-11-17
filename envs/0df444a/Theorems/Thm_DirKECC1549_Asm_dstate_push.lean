-- Prove2me | Theorems.Thm_DirKECC1549_Asm_dstate_push
-- name    : DirKECC1549.Asm.dstate_push
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-16T06:12:14.406233+00:00
-- url     : https://prove2.me/theorems/442f7a09-5e13-4c0b-bd73-16d1bd9b860a
-- title:
--   Depth-first search: following a tree edge
-- statement:
--   If the next out-edge of the top vertex $v$ (position `ptr v`) leads to an unvisited vertex $t$, advancing the pointer of $v$ and pushing $t$ keeps `DState`.
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

theorem DirKECC1549.Asm.dstate_push (D : Fin m → Fin n × Fin n) (σ : Equiv.Perm (Fin m))
    (hσ : Monotone (fun i => ((D (σ i)).1 : ℕ))) (rest po : List (Fin n)) (v : Fin n)
    (ptr : Fin n → ℕ) (h : DState D σ (rest ++ [v]) po ptr) (i : Fin m) (hi : (i : ℕ) = ptr v)
    (hp : ptr v < ots D (v + 1)) (ht1 : (D (σ i)).2 ∉ rest ++ [v]) (ht2 : (D (σ i)).2 ∉ po) :
    DState D σ (rest ++ [v] ++ [(D (σ i)).2]) po
      (Function.update (Function.update ptr v (ptr v + 1)) (D (σ i)).2 (ots D (D (σ i)).2)) := by sorry
