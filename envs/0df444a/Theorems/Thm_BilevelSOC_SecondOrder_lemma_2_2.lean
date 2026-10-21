-- Prove2me | Theorems.Thm_BilevelSOC_SecondOrder_lemma_2_2
-- name    : BilevelSOC.SecondOrder.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:47:54.704422+00:00
-- url     : https://prove2.me/theorems/ffa28a1c-24eb-479a-8428-6593f78f6eaf
-- title:
--   Lemma 2.2 — directional derivatives of a finite maximum
-- statement:
--   Let $\theta_1,\ldots,\theta_p$ be locally Lipschitz and second-order directionally differentiable at $x$, with $p\ge1$, and set $\Theta=\max_i\theta_i$. Write $I(x)=\{i:\theta_i(x)=\Theta(x)\}$ and $I(x,d)=\{i\in I(x):\theta_i'(x;d)=\Theta'(x;d)\}$. Then $\Theta$ is second-order directionally differentiable and
--   $$\Theta'(x;d)=\max_{i\in I(x)}\theta_i'(x;d),\qquad
--   \Theta''(x;d,w)=\max_{i\in I(x,d)}\theta_i''(x;d,w).$$
--   Both maxima are attained. This is the second-order calculus rule for the paper's auxiliary maximum.
--
--   **Formalization Note** The real-valued functions are Lipschitz on one neighbourhood of $x$; the source writes Lipschitz continuous extended-real functions.
-- source:
--   Mehlitz & Zemkoho, Sufficient Optimality Conditions in Bilevel Programming, arXiv:1911.01647v1, p. 5, Lemma 2.2

import Definitions.Def_BilevelSOC_SecondOrder_Model
open scoped Topology

namespace BilevelSOC.SecondOrder
theorem lemma_2_2 {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [Fintype ι] [Nonempty ι]
    (θ : ι → V → ℝ) (θ' : ι → V → ℝ) (θ'' : ι → V → V → ℝ)
    (x : V) (U : Set V) (hU : U ∈ 𝓝 x) (L : NNReal)
    (hLip : ∀ i, LipschitzOnWith L (θ i) U)
    (hDiff : ∀ i, SecondOrderDirDiff (θ i) x (θ' i) (θ'' i)) :
    ∃ (Θ' : V → ℝ) (Θ'' : V → V → ℝ),
      SecondOrderDirDiff (maxFn θ) x Θ' Θ'' ∧
      (∀ d, IsGreatest {v : ℝ | ∃ i, θ i x = maxFn θ x ∧ v = θ' i d} (Θ' d)) ∧
      (∀ d w, IsGreatest
        {v : ℝ | ∃ i, θ i x = maxFn θ x ∧ θ' i d = Θ' d ∧ v = θ'' i d w}
        (Θ'' d w)) := by sorry
end BilevelSOC.SecondOrder
