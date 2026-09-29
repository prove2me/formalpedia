-- Prove2me | Theorems.Thm_BanditAlgorithm_le_of_discounted_permutation_approximations
-- name    : BanditAlgorithm.le_of_discounted_permutation_approximations
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-31T03:41:01.112948+00:00
-- url     : https://prove2.me/theorems/43b540ae-ba3e-4cfa-8dae-5908ac60f498
-- title:
--   Dominance from finite discounted charge certificates
-- statement:
--   Let $0\leq\alpha\leq1$ and let $u,v\in\mathbb R$. Suppose that, for every $\varepsilon>0$, there are finite charge lists $x$ and $y$ such that: $x$ is a permutation of $y$; $y$ is nonincreasing; the discounted value of $x$ approximates $u$ from below up to $\varepsilon$; and the discounted value of $y$ approximates $v$ from above up to $\varepsilon$. Then $u\leq v$.
--
--   This packages the limiting step that converts finite prevailing-charge interleavings into a comparison of infinite-horizon policy values.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (CUP 2020), proof of Theorem 35.9, Part 2, printed pp.452--453, using Lemma 35.10 on printed p.451. This is the epsilon/finite-certificate limiting form of that interleaving step.

import Theorems.Thm_BanditAlgorithm_discounted_list_value_le_of_perm_pairwise

theorem BanditAlgorithm.le_of_discounted_permutation_approximations
    {α u v : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hcert : ∀ ε : ℝ, 0 < ε →
      ∃ xs ys : List ℝ,
        xs.Perm ys ∧ ys.Pairwise (· ≥ ·) ∧
        u ≤ xs.foldr (fun z acc ↦ z + α * acc) 0 + ε ∧
        ys.foldr (fun z acc ↦ z + α * acc) 0 ≤ v + ε) :
    u ≤ v := by
  sorry
