-- Prove2me | Theorems.Thm_BilevelSOC_SecondOrder_lemma_2_4
-- name    : BilevelSOC.SecondOrder.lemma_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:47:52.769278+00:00
-- url     : https://prove2.me/theorems/53c83010-fa4e-4c50-8d78-8b08ba24988a
-- title:
--   Lemma 2.4 — epi-regularity of a finite maximum
-- statement:
--   Let $\theta_1,\ldots,\theta_p$ be locally Lipschitz, second-order directionally differentiable, and second-order epi-regular at $x$, where $p\ge1$. For their pointwise maximum $\Theta=\max_i\theta_i$,
--   $$\Theta\text{ is second-order epi-regular at }x.$$
--   This preserves the regularity required by the second-order growth test when the auxiliary function is formed as a maximum.
--
--   **Formalization Note** The conclusion uses the first- and second-order derivatives of $\Theta$ itself. The real-valued and local-Lipschitz conventions are explicit.
-- source:
--   Mehlitz & Zemkoho, Sufficient Optimality Conditions in Bilevel Programming, arXiv:1911.01647v1, p. 6, Lemma 2.4

import Definitions.Def_BilevelSOC_SecondOrder_Model
open scoped Topology

namespace BilevelSOC.SecondOrder
theorem lemma_2_4 {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [Fintype ι] [Nonempty ι]
    (θ : ι → V → ℝ) (θ' : ι → V → ℝ) (θ'' : ι → V → V → ℝ)
    (x : V) (U : Set V) (hU : U ∈ 𝓝 x) (L : NNReal)
    (hLip : ∀ i, LipschitzOnWith L (θ i) U)
    (hDiff : ∀ i, SecondOrderDirDiff (θ i) x (θ' i) (θ'' i))
    (hEpi : ∀ i, SecondOrderEpiRegular (θ i) x (θ' i) (θ'' i)) :
    ∀ (Θ' : V → ℝ) (Θ'' : V → V → ℝ),
      SecondOrderDirDiff (maxFn θ) x Θ' Θ'' →
      SecondOrderEpiRegular (maxFn θ) x Θ' Θ'' := by sorry
end BilevelSOC.SecondOrder
