-- Prove2me | Theorems.Thm_ChoresTIE197_Main_lemma_B_1
-- name    : ChoresTIE197.Main.lemma_B_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T02:20:07.049363+00:00
-- url     : https://prove2.me/theorems/9cc96091-37a9-4998-b0c3-ddb5495c6be1
-- title:
--   Lemma B.1 — simultaneous two-cost balancing
-- statement:
--   Let two nonnegative additive cost functions be given on a finite set $S$, including the empty set. The contraction-and-alternation algorithm computes a disjoint partition $S=P\sqcup Q$ satisfying, simultaneously for both agents,
--   $$|c_i(P)-c_i(Q)|\le\max_{e\in S}c_i(e).$$
--   The empty maximum is zero. One deterministic program runs in polynomial input bit size on rational cost tables and implements this same routine; its correctness holds for arbitrary real costs. This is the balancing subroutine for both two-agent nomination cases.
--
--   Differences from the source:
--   - encoding: finite labelled agents and chores with complete ordered partitions and public tie breaking → Fin indices starting at zero, nonnegative real singleton tables, PMFs on owner maps, index ties; reason: every finite source instance and complete allocation is represented, including empty bundles
--   - reading: polynomial time in the input bit size for additive real costs → one binary rational bit machine with a uniform polynomial bound, plus correctness for all real costs; reason: the printed bit-complexity clause has finite rational input while its mathematical guarantee is unrestricted
--   - encoding: constructive partition or matching choices left to a public implementation → the explicitly defined public numeric choices and greedy routines; reason: these choose only from operational membership or positive-edge conditions, never from the desired fairness or incentive conclusions
-- source:
--   Zehan Lin, Biaoshuai Tao, Xiaowei Wu, Yuhao Zhang, STOC 2027 submission #859 (October 2026), Lemma B.1, printed p.34, PDF p.34; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/859.pdf

import Mathlib
import Definitions.Def_ChoresTIE197_Main_Families

open Finset Classical
open scoped NNReal ENNReal
noncomputable section

namespace ChoresTIE197.Main

theorem lemma_B_1 :
    PolyPartition (fun _ _ => True) (fun _ c => balance c univ) ∧
    ∀ m (c : Profile 2 m) (S : Finset (Fin m)),
      balance c S ⊆ S ∧ ∀ i,
        |cost (c i) (balance c S) - cost (c i) (S \ balance c S)| ≤ maximum (c i) S := by sorry

end ChoresTIE197.Main
