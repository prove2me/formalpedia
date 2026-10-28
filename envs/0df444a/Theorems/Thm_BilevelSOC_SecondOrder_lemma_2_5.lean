-- Prove2me | Theorems.Thm_BilevelSOC_SecondOrder_lemma_2_5
-- name    : BilevelSOC.SecondOrder.lemma_2_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T12:48:13.644499+00:00
-- url     : https://prove2.me/theorems/82f15e28-da6c-46d6-a80b-707ac6a26e9b
-- title:
--   Lemma 2.5 — a local minimizer has nonnegative Hadamard derivative on the tangent cone
-- statement:
--   Let $X$ be a nonempty closed set, let $x\in X$ be a local minimizer of a real function $\theta$ over $X$, and suppose $\theta$ has Hadamard directional derivatives at $x$. Then
--   $$\theta^*(x;d)\ge0\qquad(d\in T_X(x)).$$
--   This necessary condition links the feasible tangent cone to directional changes of the objective.
--
--   **Formalization Note** $T_X(x)$ is the sequential Bouligand tangent cone. The source permits extended-real $\theta$; this item uses finite real values.
-- source:
--   Mehlitz & Zemkoho, Sufficient Optimality Conditions in Bilevel Programming, arXiv:1911.01647v1, p. 6, Lemma 2.5

import Definitions.Def_BilevelSOC_SecondOrder_Model
open scoped Topology

namespace BilevelSOC.SecondOrder
theorem lemma_2_5 {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (θ : V → ℝ) (X : Set V)
    (hX : X.Nonempty) (hClosed : IsClosed X) (x : V) (hx : x ∈ X)
    (hmin : IsLocalMinOn θ X x) (θs : V → ℝ)
    (hDiff : ∀ d, HasHadamardDirDerivAt θ x d (θs d)) :
    ∀ d ∈ tangentCone X x, 0 ≤ θs d := by sorry
end BilevelSOC.SecondOrder
