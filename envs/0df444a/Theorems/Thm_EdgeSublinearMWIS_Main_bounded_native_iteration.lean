-- Prove2me | Theorems.Thm_EdgeSublinearMWIS_Main_bounded_native_iteration
-- name    : EdgeSublinearMWIS.Main.bounded_native_iteration
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-17T22:41:49.66236+00:00
-- url     : https://prove2.me/theorems/e903aec1-3a7e-4f48-8744-cbf28b3a73be
-- title:
--   Bounded iteration of finite stack programs with actual runtime
-- statement:
--   Let $U$ be a finite deterministic stack program. There is a single finite deterministic program $M$ that iterates $U$ a specified number of times. For any $n,T,V\in\mathbb N$ and sequence of binary words $v_0,\ldots,v_n$, suppose $U$ maps each $v_i$ to $v_{i+1}$ within $T$ actual steps and every word has length at most $V$. Then, given $n$ in unary followed by a delimiter and $v_0$, the program $M$ outputs $v_n$ within
--
--   $$10(n+1)(T+V+1)$$
--
--   actual stack-machine steps. The same $M$ works for all input sequences and bounds. This supplies the bounded repeated subprogram calls used in the separator-or-path-law construction.
-- source:
--   Bonnet and Chang, QPTAS for Max Weight Independent Set in Graphs with Strongly Edge-Sublinear Separators, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1044.pdf, Lemma 8 proof, pp.7–8: at most n calls to Lemma 7. This statement supplies the finite-program implementation and runtime accounting for that bounded loop.

import Definitions.Def_EdgeSublinearMWIS_Main_AlgorithmContracts
open EdgeSublinearMWIS.Main

theorem EdgeSublinearMWIS.Main.bounded_native_iteration (U : Program) :
    ∃ M : Program, ∀ (v : ℕ → List Bool) (n T V : ℕ),
      (∀ i,i< n → Runs U (v i) (v (i+1)) T) →
      (∀ i,i≤ n → (v i).length≤ V) →
      Runs M (List.replicate n true++false::v 0) (v n) (10*(n+1)*(T+V+1)) := by sorry
