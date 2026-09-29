-- Prove2me | Theorems.Thm_BanditAlgorithm_discounted_list_value_le_of_perm_pairwise
-- name    : BanditAlgorithm.discounted_list_value_le_of_perm_pairwise
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-31T03:37:49.494576+00:00
-- url     : https://prove2.me/theorems/05f17b16-17c1-408b-9379-dabec709ca83
-- title:
--   Finite discounted interleaving inequality
-- statement:
--   Let $0\leq \alpha\leq 1$, and let $x$ and $y$ be finite lists of real charges containing the same multiset of entries. If $y$ is arranged in nonincreasing order, then its discounted value is at least that of $x$:
--
--   $$
--   x_0+\alpha x_1+\cdots+\alpha^{n-1}x_{n-1}
--   \;\leq\;
--   y_0+\alpha y_1+\cdots+\alpha^{n-1}y_{n-1}.
--   $$
--
--   This is the finite deterministic exchange inequality underlying the interleaving argument for prevailing charges.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (CUP 2020), Lemma 35.10 and its use in the proof of Theorem 35.9, printed pp.451--453. This theorem is the finite permutation/exchange core of that lemma.

import Mathlib.Data.List.Perm.Basic
import Mathlib.Tactic

theorem BanditAlgorithm.discounted_list_value_le_of_perm_pairwise
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    {xs ys : List ℝ} (hperm : xs.Perm ys)
    (hsorted : ys.Pairwise (· ≥ ·)) :
    xs.foldr (fun z acc ↦ z + α * acc) 0 ≤
      ys.foldr (fun z acc ↦ z + α * acc) 0 := by
  sorry
