-- Prove2me | Theorems.Thm_DirKECC1549_Asm_kosaraju_key
-- name    : DirKECC1549.Asm.kosaraju_key
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-16T06:12:11.224082+00:00
-- url     : https://prove2.me/theorems/230f8bcd-4f0e-4cd9-b90e-28456d3318db
-- title:
--   Kosaraju's key property
-- statement:
--   If the positions `pos` satisfy the post-order property (`KP`: every edge leaving a vertex either goes to a vertex finished later or to one that reaches back), then within a set $U$ closed under strong connectivity, a vertex $v$ of maximal position is reached only by vertices it reaches: $u\in U$, $u\leadsto v$ imply $v\leadsto u$.
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

theorem DirKECC1549.Asm.kosaraju_key (D : Fin m → Fin n × Fin n) (pos : Fin n → ℕ) (hpos : Function.Injective pos)
    (hKP : KP D pos) (U : Finset (Fin n))
    (hU : ∀ a b, StronglyConn D a b → a ∈ U → b ∈ U) (v : Fin n) (hv : v ∈ U)
    (hmax : ∀ x ∈ U, pos x ≤ pos v) (u : Fin n) (hu : u ∈ U) (huv : Reach D u v) :
    Reach D v u := by sorry
