-- Prove2me | Theorems.Thm_DirKECC1549_Asm_dfsH_finish
-- name    : DirKECC1549.Asm.dfsH_finish
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-16T06:12:29.444213+00:00
-- url     : https://prove2.me/theorems/59918f78-0c43-4170-87f7-74ca3079b101
-- title:
--   Finishing a vertex of the depth-first search keeps the post-order invariant
-- statement:
--   When the gray vertex $z$ (all of whose out-neighbours are finished or gray, and every gray vertex reaching $z$) is finished with a position larger than all earlier ones, the invariant `DfsH` of the finished set and positions extends to $\mathrm{fin}\cup\{z\}$.
--
--   **Context.** This lemma belongs to the machine-checked word-RAM implementation of the strongly connected components computation used by Algorithm 3 (the child contract `scc_impl`): Kosaraju's algorithm with an iterative depth-first search on $D$ producing the post-order (pass 1), followed by searches on reversed edges from the vertices in decreasing post-order, each labelling one component (pass 2), all in $O(n+m)$ ticks on the graph layout.
-- source:
--   Loukas Georgiadis, Evangelos Kipouridis, Evangelos Kosinas, Charis Papadopoulos, Christos Pergaminelis, STOC 2027 submission #1549 (October 2026), Section 3.3, Algorithm 3 (p.17) and proof of Lemma 5 (pp.18–19); word-RAM model of Hagerup (p.25). Implementation-level lemma of the verified program for Lemma 5.

import Definitions.Def_DirKECC1549_Impl_SccMath

set_option autoImplicit false
open Classical Finset
open DirKECC1549.Main DirKECC1549.Main.CostAux
open DirKECC1549 DirKECC1549.Asm
variable {n m : ℕ}

theorem DirKECC1549.Asm.dfsH_finish (D : Fin m → Fin n × Fin n) (fin : Finset (Fin n)) (pos : Fin n → ℕ)
    (gray : Finset (Fin n)) (z : Fin n) (hz : z ∉ fin) (hzg : z ∈ gray)
    (hdisj : ∀ x ∈ fin, x ∉ gray)
    (hH : DfsH D fin pos)
    (hS2 : ∀ e, (D e).1 ∈ insert z fin → (D e).2 ∈ insert z fin ∨ (D e).2 ∈ gray)
    (hchain : ∀ g ∈ gray, Reach D g z)
    (pz : ℕ) (hpz : ∀ x ∈ fin, pos x < pz) :
    DfsH D (insert z fin) (Function.update pos z pz) := by sorry
