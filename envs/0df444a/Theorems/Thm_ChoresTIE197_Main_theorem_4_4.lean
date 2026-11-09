-- Prove2me | Theorems.Thm_ChoresTIE197_Main_theorem_4_4
-- name    : ChoresTIE197.Main.theorem_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T02:19:49.933464+00:00
-- url     : https://prove2.me/theorems/0e52f3a7-ee6f-4704-8b79-1cddcfb8e2b7
-- title:
--   Theorem 4.4 — large-n equal-marginal 1.97-MMS mechanism
-- statement:
--   For every $n\ge19$, the complete Section 4 mechanism has equal marginals at every admissible profile and is truthful in expectation, ex-ante envy-free, and ex-post $197/100$-MMS:
--   $$\Pr[e\in X_i]=1/n,\qquad c_i(X_i)\le\frac{197}{100}\mu_i\quad\text{for every supported }X.$$
--   The incentive and envy comparisons are evaluated with each agent's true row and range over every admissible alternative report. A uniform exact rational-input sampler implements this law in expected polynomial bit time. Every real nonnegative positive-MMS profile is covered, including zero item costs and all three cases of the derived hard set. This theorem is not restricted to the range $n\ge66$ used to assemble the headline.
--
--   Differences from the source:
--   - encoding: finite labelled agents and chores with complete ordered partitions and public tie breaking → Fin indices starting at zero, nonnegative real singleton tables, PMFs on owner maps, index ties; reason: every finite source instance and complete allocation is represented, including empty bundles
--   - encoding: standing positive-MMS convention on p.7 → each nonnegative cost row has positive total cost; reason: for n greater than zero on finite nonnegative instances, positive total cost and positive MMS are equivalent; individual zero item costs remain allowed
--   - reading: polynomial-time randomized mechanism → almost-surely terminating exact fair-bit sampler with uniform expected polynomial charged steps on rational reports, with correctness for all real costs; reason: p.12 explicitly uses expected-time rejection sampling; finite bit tapes cannot realize arbitrary rational probabilities in bounded time
--   - encoding: constructive partition or matching choices left to a public implementation → the explicitly defined public numeric choices and greedy routines; reason: these choose only from operational membership or positive-edge conditions, never from the desired fairness or incentive conclusions
--   - encoding: there exists a sorted-slot decomposition, deleting empty slots → the explicit positive-support greedy Birkhoff law with m+1 slots per agent, unused slots filled by dummy chores; reason: additional empty slots cannot receive any real chore, and no bound is assumed to select the law
-- source:
--   Zehan Lin, Biaoshuai Tao, Xiaowei Wu, Yuhao Zhang, STOC 2027 submission #859 (October 2026), Theorem 4.4, printed p.23, PDF p.23; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/859.pdf

import Mathlib
import Definitions.Def_ChoresTIE197_Main_Families

open Finset Classical
open scoped NNReal ENNReal
noncomputable section

namespace ChoresTIE197.Main

theorem theorem_4_4 :
    PolySampler (fun n _ k c => 19 ≤ n ∧ k = 0 ∧ Positive c) largeFamily ∧
    ∀ n m [NeZero n], 19 ≤ n →
      EqualOn Positive (@mechanism4 n m _) ∧
      TIEOn Positive (@mechanism4 n m _) ∧
      EFOn Positive (@mechanism4 n m _) ∧
      MMSOn Positive (197/100:ℝ) (@mechanism4 n m _) := by sorry

end ChoresTIE197.Main
