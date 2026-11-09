-- Prove2me | Theorems.Thm_ChoresTIE197_Main_lemma_3_4
-- name    : ChoresTIE197.Main.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T02:20:25.500475+00:00
-- url     : https://prove2.me/theorems/b8aea1ce-03e7-4acd-bc34-798cb1c1eb4a
-- title:
--   Lemma 3.4 — safety and exact nomination marginals
-- statement:
--   For every $n\ge3$, $1\le k<n$ and admissible reported profile, every realized allocation of Mechanism 2 is safe: each agent receives either at most one chore or only non-nominated chores with at most one per residual block. In the same law,
--   $$\Pr[e\in X_i]=\frac{l(e)-1+n\,\mathbf1[e\notin H_{i,[k]}]}{n(n-1)}\qquad(i\in N,e\in M).$$
--   Here $l(e)$ counts nominations from all agents at this profile. The indicator is nonmembership, and the subtraction occurs in real numbers. Both safety and the exact formula are conclusions, not assumptions on the mechanism.
--
--   Differences from the source:
--   - encoding: finite labelled agents and chores with complete ordered partitions and public tie breaking → Fin indices starting at zero, nonnegative real singleton tables, PMFs on owner maps, index ties; reason: every finite source instance and complete allocation is represented, including empty bundles
--   - encoding: standing positive-MMS convention on p.7 → each nonnegative cost row has positive total cost; reason: for n greater than zero on finite nonnegative instances, positive total cost and positive MMS are equivalent; individual zero item costs remain allowed
--   - encoding: constructive partition or matching choices left to a public implementation → the explicitly defined public numeric choices and greedy routines; reason: these choose only from operational membership or positive-edge conditions, never from the desired fairness or incentive conclusions
--   - encoding: public zero dummy padding before reports → dimension-dependent forced zero extension and removal, with all subsets and ranks computed from the actual reports; reason: dummy reports cannot be manipulated and the displayed formula concerns each original chore
-- source:
--   Zehan Lin, Biaoshuai Tao, Xiaowei Wu, Yuhao Zhang, STOC 2027 submission #859 (October 2026), Lemma 3.4, printed p.10, PDF p.10; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/859.pdf

import Mathlib
import Definitions.Def_ChoresTIE197_Main_Families

open Finset Classical
open scoped NNReal ENNReal
noncomputable section

namespace ChoresTIE197.Main

theorem lemma_3_4 {n m : ℕ} [NeZero n] (hn : 3 ≤ n) (k : ℕ)
    (hk : 1 ≤ k) (hkn : k < n) (c : Profile n m) (hc : Positive c) :
    (∀ A, mechanism2 k c A ≠ 0 → Safe c k A) ∧
    ∀ i e, marginal (mechanism2 k c) i e =
      ((nominations c k e : ℝ) - 1 + (n:ℝ)*(if e ∉ top (c i) k then 1 else 0)) /
        ((n:ℝ)*((n:ℝ)-1)) := by sorry

end ChoresTIE197.Main
