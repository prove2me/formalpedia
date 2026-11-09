-- Prove2me | Theorems.Thm_ChoresTIE197_Main_lemma_B_3
-- name    : ChoresTIE197.Main.lemma_B_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T02:19:35.652128+00:00
-- url     : https://prove2.me/theorems/6ceb10e5-738e-426c-879d-8ee4b45d8538
-- title:
--   Lemma B.3 — distinct-nomination partition
-- statement:
--   For two positive-MMS agents, let their publicly selected top nominations $e_1,e_2$ be distinct. The residual balancing routine computes a disjoint partition $M\setminus\{e_1,e_2\}=P\sqcup Q$ with
--   $$\max\{c_i(P\cup\{e_{3-i}\}),c_i(Q\cup\{e_{3-i}\})\}\le\frac54\mu_i\qquad(i=1,2).$$
--   The routine has a uniform deterministic polynomial-time bit implementation on rational tables and is correct for all real costs in the source domain. The empty residual set is allowed. The stronger printed constant $5/4$ is retained although Mechanism 3 only needs $4/3$.
--
--   Differences from the source:
--   - encoding: finite labelled agents and chores with complete ordered partitions and public tie breaking → Fin indices starting at zero, nonnegative real singleton tables, PMFs on owner maps, index ties; reason: every finite source instance and complete allocation is represented, including empty bundles
--   - encoding: standing positive-MMS convention on p.7 → each nonnegative cost row has positive total cost; reason: for n greater than zero on finite nonnegative instances, positive total cost and positive MMS are equivalent; individual zero item costs remain allowed
--   - reading: polynomial time in the input bit size for additive real costs → one binary rational bit machine with a uniform polynomial bound, plus correctness for all real costs; reason: the printed bit-complexity clause has finite rational input while its mathematical guarantee is unrestricted
--   - encoding: constructive partition or matching choices left to a public implementation → the explicitly defined public numeric choices and greedy routines; reason: these choose only from operational membership or positive-edge conditions, never from the desired fairness or incentive conclusions
-- source:
--   Zehan Lin, Biaoshuai Tao, Xiaowei Wu, Yuhao Zhang, STOC 2027 submission #859 (October 2026), Lemma B.3, printed p.36, PDF p.36; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/859.pdf

import Mathlib
import Definitions.Def_ChoresTIE197_Main_Families

open Finset Classical
open scoped NNReal ENNReal
noncomputable section

namespace ChoresTIE197.Main

theorem lemma_B_3 :
    PolyPartition (fun m c => 0 < m ∧ Positive c ∧
      Disjoint (top (c 0) 1) (top (c 1) 1)) distinctFamily ∧
    ∀ m [NeZero m] (c : Profile 2 m), Positive c →
      nominee (c 0) ≠ nominee (c 1) →
      let R := univ \ {nominee (c 0), nominee (c 1)}
      let P := distinctPartition c
      P ⊆ R ∧ ∀ i : Fin 2,
        let other : Fin 2 := if i = 0 then 1 else 0
        let e := nominee (c other)
        max (cost (c i) (insert e P)) (cost (c i) (insert e (R \ P))) ≤
          (5/4:ℝ) * mms (c i) 2 univ := by sorry

end ChoresTIE197.Main
