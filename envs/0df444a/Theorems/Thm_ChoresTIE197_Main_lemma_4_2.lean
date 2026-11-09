-- Prove2me | Theorems.Thm_ChoresTIE197_Main_lemma_4_2
-- name    : ChoresTIE197.Main.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T02:19:58.201206+00:00
-- url     : https://prove2.me/theorems/2f49c34d-aed2-4d3a-8c18-94aef59418a2
-- title:
--   Lemma 4.2 — sorted-slot decomposition and both bounds
-- statement:
--   Let $x$ be an arbitrary nonnegative real matrix with $\sum_i x_{ie}=1$ for every chore. The sorted-slot distribution preserves every fractional marginal exactly: $\Pr[e\in X_i]=x_{ie}$. Every allocation in this one distribution's support satisfies
--   $$c_i(X_i)\le\max_{e:x_{ie}>0}c_i(e)+\sum_e x_{ie}c_i(e).$$
--   For each individual agent with $|M|>n$ and $\sum_{e\in H_{i,[n]}}x_{ie}=1$, the same distribution also satisfies
--   $$c_i(X_i)\le c_{i,(1)}+c_{i,(n+1)}+\sum_{e\notin H_{i,[n]}}x_{ie}c_i(e).$$
--   Zero fractional rows receive no chores, with maximum zero. No shared ranking, rationality restriction, row-sum assumption or runtime assertion is added.
--
--   Differences from the source:
--   - encoding: finite labelled agents and chores with complete ordered partitions and public tie breaking → Fin indices starting at zero, nonnegative real singleton tables, PMFs on owner maps, index ties; reason: every finite source instance and complete allocation is represented, including empty bundles
--   - encoding: there exists a sorted-slot decomposition, deleting empty slots → the explicit positive-support greedy Birkhoff law with m+1 slots per agent, unused slots filled by dummy chores; reason: additional empty slots cannot receive any real chore, and no bound is assumed to select the law
--   - generalization: p.7 positive-MMS standing convention → Lemma 4.2 also allows zero cost rows; reason: the Appendix A construction and both bounds depend only on cost order and nonnegativity, so the source domain is included
-- source:
--   Zehan Lin, Biaoshuai Tao, Xiaowei Wu, Yuhao Zhang, STOC 2027 submission #859 (October 2026), Lemma 4.2, printed p.15, PDF p.15; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/859.pdf

import Mathlib
import Definitions.Def_ChoresTIE197_Main_Families

open Finset Classical
open scoped NNReal ENNReal
noncomputable section

namespace ChoresTIE197.Main

theorem lemma_4_2 {n m : ℕ} [NeZero n] (c : Profile n m)
    (x : Fraction n m) (hx : Feasible x) :
    (∀ i e, marginal (roundSlots c x) i e = x i e) ∧
    ∀ A, roundSlots c x A ≠ 0 → ∀ i,
      cost (c i) (bundle A i) ≤
        maximum (c i) (univ.filter (fun e => 0 < x i e)) + fractionalCost c x i univ ∧
      (n < m → (∑ e ∈ top (c i) n, x i e) = 1 →
        cost (c i) (bundle A i) ≤ kth (c i) 1 + kth (c i) (n+1) +
          fractionalCost c x i (univ \ top (c i) n)) := by sorry

end ChoresTIE197.Main
