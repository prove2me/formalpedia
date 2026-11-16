-- Prove2me | Theorems.Thm_DirKECC1549_Main_CostAux_induced_scc_sc
-- name    : DirKECC1549.Main.CostAux.induced_scc_sc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-16T03:52:12.553591+00:00
-- url     : https://prove2.me/theorems/943e09a2-ccd5-4d6c-a79f-2a4d3d162a31
-- title:
--   The induced subgraph of a strongly connected component is strongly connected
-- statement:
--   For every multigraph $D$ and vertex $u$, the induced subgraph $D[S]$ on the strongly connected component $S$ of $u$ (vertices renamed in increasing order) is strongly connected, given that walks between vertices of $S$ stay in $S$ and lift to the induced subgraph (the facts `walks_in_scc` and `induced_walk_lift`, passed as hypotheses).
--
--   **Context.** This lemma belongs to the machine-checked word-RAM implementation of Algorithm 3 (`kEdgeConnectedComponents`, p.17) that proves `lemma_5_impl`. The program is written in a small structured language (`Stmt`: straight-line code, sequencing, conditionals, loops, calls of one recursive procedure, and sandboxed calls of black-box subroutines) compiled to the published word-RAM; `Run E s mem Q` states that the statement `s`, compiled anywhere in the program described by the environment `E`, started on memory `mem`, reaches its end in a state satisfying `Q t mem'`, where `t` is the number of ticks spent. All definitions are in the `Definitions.Def_DirKECC1549_Impl_*` modules.
-- source:
--   Loukas Georgiadis, Evangelos Kipouridis, Evangelos Kosinas, Charis Papadopoulos, Christos Pergaminelis, STOC 2027 submission #1549 (October 2026), Section 3.3, Algorithm 3 (p.17) and proof of Lemma 5 (pp.18–19); word-RAM model of Hagerup (p.25). Implementation-level lemma of the verified program for Lemma 5.

import Definitions.Def_DirKECC1549_Impl_GraphAux

set_option autoImplicit false
open Classical Finset
open DirKECC1549.Main
open DirKECC1549 DirKECC1549.Main.CostAux
variable {n m : ℕ}

theorem DirKECC1549.Main.CostAux.induced_scc_sc (hF : DirKECC1549.Asm.Facts) (D : Fin m → Fin n × Fin n) (u : Fin n) :
    IsStronglyConnected (induced D (sccOf D u)) := by sorry
