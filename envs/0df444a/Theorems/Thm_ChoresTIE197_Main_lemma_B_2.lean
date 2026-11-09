-- Prove2me | Theorems.Thm_ChoresTIE197_Main_lemma_B_2
-- name    : ChoresTIE197.Main.lemma_B_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T02:21:16.015145+00:00
-- url     : https://prove2.me/theorems/4422e9b4-9886-40f1-b4fa-56b7ab2b492f
-- title:
--   Lemma B.2 — common-nomination partition
-- statement:
--   For two agents with positive MMS, suppose the two public top nominations coincide at $e$. The common-nomination routine computes $P\subseteq M\setminus\{e\}$ such that both complementary parts obey, for each agent,
--   $$\max\{c_i(P\cup\{e\}),c_i(M\setminus(P\cup\{e\}))\}\le\frac43\mu_i.$$
--   A single deterministic bit algorithm computes this partition in polynomial input bit size on rational tables. Correctness includes all real nonnegative costs satisfying the source's standing convention. Both parts and both agents are covered; this is the shared-nomination branch of Mechanism 3.
--
--   Differences from the source:
--   - encoding: finite labelled agents and chores with complete ordered partitions and public tie breaking → Fin indices starting at zero, nonnegative real singleton tables, PMFs on owner maps, index ties; reason: every finite source instance and complete allocation is represented, including empty bundles
--   - encoding: standing positive-MMS convention on p.7 → each nonnegative cost row has positive total cost; reason: for n greater than zero on finite nonnegative instances, positive total cost and positive MMS are equivalent; individual zero item costs remain allowed
--   - reading: polynomial time in the input bit size for additive real costs → one binary rational bit machine with a uniform polynomial bound, plus correctness for all real costs; reason: the printed bit-complexity clause has finite rational input while its mathematical guarantee is unrestricted
--   - encoding: constructive partition or matching choices left to a public implementation → the explicitly defined public numeric choices and greedy routines; reason: these choose only from operational membership or positive-edge conditions, never from the desired fairness or incentive conclusions
-- source:
--   Zehan Lin, Biaoshuai Tao, Xiaowei Wu, Yuhao Zhang, STOC 2027 submission #859 (October 2026), Lemma B.2, printed p.35, PDF p.35; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/859.pdf

import Mathlib
import Definitions.Def_ChoresTIE197_Main_Families

open Finset Classical
open scoped NNReal ENNReal
noncomputable section

namespace ChoresTIE197.Main

theorem lemma_B_2 :
    PolyPartition (fun m c => 0 < m ∧ Positive c ∧
      ∃ e, top (c 0) 1 = {e} ∧ top (c 1) 1 = {e}) commonFamily ∧
    ∀ m [NeZero m] (c : Profile 2 m), Positive c →
      nominee (c 0) = nominee (c 1) →
      let e := nominee (c 0)
      let P := commonPartition c
      P ⊆ univ \ {e} ∧ ∀ i,
        max (cost (c i) (insert e P)) (cost (c i) (univ \ insert e P)) ≤
          (4/3:ℝ) * mms (c i) 2 univ := by sorry

end ChoresTIE197.Main
