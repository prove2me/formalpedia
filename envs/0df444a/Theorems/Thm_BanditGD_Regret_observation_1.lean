-- Prove2me | Theorems.Thm_BanditGD_Regret_observation_1
-- name    : BanditGD.Regret.observation_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T08:04:50.539972+00:00
-- url     : https://prove2.me/theorems/86d7dab5-e152-4210-b505-981fc07b8e6e
-- title:
--   Observation 1, p. 7 — min over (1−α)S is at most 2αCn above min over S
-- statement:
--   Let $S\subseteq\mathbb R^d$ be convex with $0\in S$, let $C\in\mathbb R$, and let $c_1,c_2,\dots:\mathbb R^d\to\mathbb R$ be convex on $S$ with $|c_t(x)|\le C$ for all $x\in S$. For every $\alpha\in[0,1]$ and every $n$,
--   $$\min_{x\in(1-\alpha)S}\sum_{t=1}^n c_t(x)\le 2\alpha Cn+\min_{x\in S}\sum_{t=1}^n c_t(x).$$
--
--   Running the algorithm on the shrunk set $(1-\alpha)S$, which keeps the sampling sphere inside $S$, therefore costs at most $2\alpha Cn$ in the comparator.
--
--   **Formalization Note** Both minima are written as infima over the sets; both sets are nonempty (they contain $0$) and every sum is at least $-nC$, so neither infimum is a junk value. The paper's $C>0$ is not needed and not assumed.
-- source:
--   Flaxman, Kalai, McMahan, arXiv:cs/0408007v1, p. 7, Observation 1

import Mathlib
open scoped Pointwise

namespace BanditGD.Regret

theorem observation_1 {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d))) (hSconv : Convex ℝ S)
    (h0S : (0 : EuclideanSpace ℝ (Fin d)) ∈ S) (C : ℝ) (c : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (hcconv : ∀ t, ConvexOn ℝ S (c t)) (hcbdd : ∀ t, ∀ x ∈ S, |c t x| ≤ C)
    (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (n : ℕ) :
    (⨅ x : ((1 - α) • S : Set (EuclideanSpace ℝ (Fin d))), ∑ t ∈ Finset.Icc 1 n, c t x)
      ≤ 2 * α * C * n + ⨅ x : S, ∑ t ∈ Finset.Icc 1 n, c t x := by sorry

end BanditGD.Regret
