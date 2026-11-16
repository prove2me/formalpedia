-- Prove2me | Theorems.Thm_DirKECC1549_Asm_sc_n_le_m
-- name    : DirKECC1549.Asm.sc_n_le_m
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-16T03:52:56.497828+00:00
-- url     : https://prove2.me/theorems/a4972d44-9c48-4952-a0f5-d239d694ee3e
-- title:
--   A strongly connected multigraph with $n\ge2$ vertices has at least $n$ edges
-- statement:
--   If $D$ is strongly connected and $n\ge2$, every vertex has an outgoing edge (to reach any other vertex), so $n\le m$.
--
--   **Context.** This lemma belongs to the machine-checked word-RAM implementation of Algorithm 3 (`kEdgeConnectedComponents`, p.17) that proves `lemma_5_impl`. The program is written in a small structured language (`Stmt`: straight-line code, sequencing, conditionals, loops, calls of one recursive procedure, and sandboxed calls of black-box subroutines) compiled to the published word-RAM; `Run E s mem Q` states that the statement `s`, compiled anywhere in the program described by the environment `E`, started on memory `mem`, reaches its end in a state satisfying `Q t mem'`, where `t` is the number of ticks spent. All definitions are in the `Definitions.Def_DirKECC1549_Impl_*` modules.
-- source:
--   Loukas Georgiadis, Evangelos Kipouridis, Evangelos Kosinas, Charis Papadopoulos, Christos Pergaminelis, STOC 2027 submission #1549 (October 2026), Section 3.3, Algorithm 3 (p.17) and proof of Lemma 5 (pp.18–19); word-RAM model of Hagerup (p.25). Implementation-level lemma of the verified program for Lemma 5.

import Definitions.Def_DirKECC1549_Impl_MainMath

set_option autoImplicit false
open Classical Finset DirKECC1549.Main
open DirKECC1549 DirKECC1549.Asm
variable {n m : ℕ}

theorem DirKECC1549.Asm.sc_n_le_m (D : Fin m → Fin n × Fin n) (h : IsStronglyConnected D) (hn : 2 ≤ n) :
    n ≤ m := by sorry
