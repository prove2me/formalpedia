-- Prove2me | Theorems.Thm_AggCG_Supplement_theorem_G_5
-- name    : AggCG.Supplement.theorem_G_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T23:32:31.933245+00:00
-- url     : https://prove2.me/theorems/915e6d59-b955-406d-a329-4770d117a954
-- title:
--   Theorem G.5 — constant-margin matching lower bound
-- statement:
--   For the dyadic online-matching policy and the $T$ evaluation instances whose final arrival is adjacent only to $A_i$, normalized regret satisfies
--
--   $$
--   \operatorname{fat}_{1/4}(F_T)\ge T.
--   $$
--
--   The construction uses one scalar parameter and exactly $3T+1$ vertices and $2T+1$ edges per instance, hence linear size with one uniform constant.
--
--   Differences from the source: none.
-- source:
--   Sharma, STOC 2027 submission (manuscript sha256 f7ea0248…), Theorem G.5, p.44, PDF p.45

import Mathlib
import Definitions.Def_BartlettNN_Margin_FatShattering
import Definitions.Def_AggCG_Supplement_matchLoss

namespace AggCG.Supplement

/-- **Theorem G.5** (Constant-margin matching lower bound; Sharma, *Computational Complexity of Data-Driven
Configuration for Integer Programming, Clustering, and Learning Algorithms*, STOC 2027 submission
(manuscript sha256 f7ea0248…), p.44, PDF p.45). For the dyadic policy of §G.4 and the evaluation
instances `x_i` whose final arrival has weight `1` and is adjacent only to `A_i`, the normalized regret
`f_θ(x) = 1 − ALG_θ(x)/OPT(x)` with one real parameter `θ ∈ [0, 1]` `1/4`-fat-shatters `x_1, …, x_T`, so
`fat_{1/4}(F_T) ≥ T`; each instance has `3T + 1` vertices and `2T + 1` edges, `O(T)` with one absolute
constant.

**Formalization Note** The parameter ranges over `[0, 1]`, a subset of the paper's real line, so the
lower bound is for a smaller class and implies the paper's. -/
theorem theorem_G_5 :
    (∀ T : ℕ, BartlettNN.Margin.GammaShatters
        {g : Finset (Offline T) → ℝ | ∃ θ ∈ Set.Icc (0 : ℝ) 1, g = matchLoss T θ} (1 / 4)
        (fun i : Fin T => ({(i, true)} : Finset (Offline T)))) ∧
    (∀ (T : ℕ) (i : Fin T),
      Fintype.card (Offline T) + (probeInst T {(i, true)}).k = 3 * T + 1 ∧
        ∑ a, ((probeInst T {(i, true)}).nbr a).card = 2 * T + 1) ∧
    ∃ C : ℕ, ∀ T : ℕ, 3 * T + 1 ≤ C * (T + 1) ∧ 2 * T + 1 ≤ C * (T + 1) := by sorry

end AggCG.Supplement
