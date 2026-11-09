-- Prove2me | Theorems.Thm_ChoresTIE197_Main_theorem_3_5
-- name    : ChoresTIE197.Main.theorem_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T02:19:55.050923+00:00
-- url     : https://prove2.me/theorems/b4692d67-6672-467e-ab6a-b8e20ef1517c
-- title:
--   Theorem 3.5 — the full k-nomination guarantee
-- statement:
--   For every $n\ge3$ and every integer $1\le k\le\lfloor(n-1)/2\rfloor$, Mechanism 2 is truthful in expectation, ex-ante envy-free and ex-post
--   $$\left(2-\frac1{n-k}\right)\text{-MMS}.$$
--   The cost bound holds for every agent in every supported complete allocation, under the positive-MMS standing convention. One exact rational-input sampler, chosen uniformly before $n,m,k$ and the reports, implements this law in expected polynomial bit time. Mathematical correctness ranges over all nonnegative real costs in the source domain. The entire printed k range is preserved.
--
--   Differences from the source:
--   - encoding: finite labelled agents and chores with complete ordered partitions and public tie breaking → Fin indices starting at zero, nonnegative real singleton tables, PMFs on owner maps, index ties; reason: every finite source instance and complete allocation is represented, including empty bundles
--   - encoding: standing positive-MMS convention on p.7 → each nonnegative cost row has positive total cost; reason: for n greater than zero on finite nonnegative instances, positive total cost and positive MMS are equivalent; individual zero item costs remain allowed
--   - reading: polynomial-time randomized mechanism → almost-surely terminating exact fair-bit sampler with uniform expected polynomial charged steps on rational reports, with correctness for all real costs; reason: p.12 explicitly uses expected-time rejection sampling; finite bit tapes cannot realize arbitrary rational probabilities in bounded time
--   - encoding: constructive partition or matching choices left to a public implementation → the explicitly defined public numeric choices and greedy routines; reason: these choose only from operational membership or positive-edge conditions, never from the desired fairness or incentive conclusions
-- source:
--   Zehan Lin, Biaoshuai Tao, Xiaowei Wu, Yuhao Zhang, STOC 2027 submission #859 (October 2026), Theorem 3.5, printed p.12, PDF p.12; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/859.pdf

import Mathlib
import Definitions.Def_ChoresTIE197_Main_Families

open Finset Classical
open scoped NNReal ENNReal
noncomputable section

namespace ChoresTIE197.Main

theorem theorem_3_5 :
    PolySampler (fun n _ k c => 3 ≤ n ∧ 1 ≤ k ∧ k ≤ (n-1)/2 ∧ Positive c)
      nominationFamily ∧
    ∀ n m [NeZero n], 3 ≤ n → ∀ k, 1 ≤ k → k ≤ (n-1)/2 →
      TIEOn Positive (@mechanism2 n m _ k) ∧
      EFOn Positive (@mechanism2 n m _ k) ∧
      MMSOn Positive (2 - 1/((n:ℝ)-k)) (@mechanism2 n m _ k) := by sorry

end ChoresTIE197.Main
