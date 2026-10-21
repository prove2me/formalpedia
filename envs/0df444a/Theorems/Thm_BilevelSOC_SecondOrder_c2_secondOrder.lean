-- Prove2me | Theorems.Thm_BilevelSOC_SecondOrder_c2_secondOrder
-- name    : BilevelSOC.SecondOrder.c2_secondOrder
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:48:04.78848+00:00
-- url     : https://prove2.me/theorems/6d774dfd-75ea-4e74-bc8f-ac7c7a7c0c28
-- title:
--   (2.2) and p. 6 — $C^2$ functions have the second-order derivative formula and are epi-regular
-- statement:
--   Let $\theta$ be a twice continuously differentiable real function on a finite-dimensional normed space. At every point $x$ it is second-order directionally differentiable and second-order epi-regular, with
--   $$\theta''(x;d,w)=D\theta(x)[w]+D^2\theta(x)[d,d].$$
--   This identifies the smooth terms in the maximum used by Theorem 5.3.
--
--   **Formalization Note** The source states the result on Euclidean space; the statement uses a finite-dimensional real normed space and global $C^2$ regularity.
-- source:
--   Mehlitz & Zemkoho, Sufficient Optimality Conditions in Bilevel Programming, arXiv:1911.01647v1, pp. 5–6, (2.2) and first paragraph of p. 6

import Definitions.Def_BilevelSOC_SecondOrder_Model
open scoped Topology

namespace BilevelSOC.SecondOrder
theorem c2_secondOrder {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (θ : V → ℝ) (hθ : ContDiff ℝ 2 θ) (x : V) :
    SecondOrderDirDiff θ x (fun d => fderiv ℝ θ x d)
      (fun d w => fderiv ℝ θ x w + fderiv ℝ (fderiv ℝ θ) x d d) ∧
    SecondOrderEpiRegular θ x (fun d => fderiv ℝ θ x d)
      (fun d w => fderiv ℝ θ x w + fderiv ℝ (fderiv ℝ θ) x d d) := by sorry
end BilevelSOC.SecondOrder
