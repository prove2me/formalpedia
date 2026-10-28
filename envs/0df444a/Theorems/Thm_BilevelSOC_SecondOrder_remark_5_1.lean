-- Prove2me | Theorems.Thm_BilevelSOC_SecondOrder_remark_5_1
-- name    : BilevelSOC.SecondOrder.remark_5_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T12:48:02.639426+00:00
-- url     : https://prove2.me/theorems/5aab063b-0098-4a07-aba5-e307cf5a028c
-- title:
--   Remark 5.1 — ACQ makes the value-function inequality active on the cone
-- statement:
--   At a feasible bilevel point $(\bar x,\bar y)$, suppose the value function $\varphi$ is locally Lipschitz and directionally differentiable, and ACQ holds for $\{(x,y):g(x,y)\le0\}$. Every direction $d=(\delta_x,\delta_y)$ satisfying the active linearized lower-level constraints obeys
--   $$Df(\bar x,\bar y)[d]-\varphi'(\bar x;\delta_x)\ge0.$$
--   Consequently the inequality defining $L_M^\varphi$ through $f-\varphi$ is an equality there. This identifies the active term used in the second-order test.
--
--   **Formalization Note** A real function represents the extended-real value function on a neighbourhood. The standing $C^2$ assumption on the data is explicit.
-- source:
--   Mehlitz & Zemkoho, Sufficient Optimality Conditions in Bilevel Programming, arXiv:1911.01647v1, pp. 18–19, Remark 5.1 and (5.3)

import Definitions.Def_BilevelSOC_SecondOrder_Model
open scoped Topology

namespace BilevelSOC.SecondOrder
theorem remark_5_1 {n m p q : ℕ} (D : Data n m p q) (hD : Standing D)
    (xbar : E n) (ybar : Y m) (hfeas : (xbar, ybar) ∈ feasSet D)
    (φr : E n → ℝ) (U : Set (E n)) (hU : U ∈ 𝓝 xbar)
    (hφU : ∀ x ∈ U, valueFn D x = (φr x : EReal))
    (L : NNReal) (hLip : LipschitzOnWith L φr U)
    (φ' : E n → ℝ) (hφDiff : ∀ d, HasDirDerivAt φr xbar d (φ' d))
    (hACQ : ACQ52 D (xbar, ybar)) :
    (∀ d : E n × Y m,
      (∀ j ∈ actg D (xbar, ybar), fderiv ℝ (D.g j) (xbar, ybar) d ≤ 0) →
      0 ≤ fderiv ℝ D.f (xbar, ybar) d - φ' d.1) ∧
    linConeVF D (xbar, ybar) φ' =
      {d | (∀ i ∈ actG D (xbar, ybar), fderiv ℝ (D.G i) (xbar, ybar) d ≤ 0) ∧
        fderiv ℝ D.f (xbar, ybar) d - φ' d.1 = 0 ∧
        ∀ j ∈ actg D (xbar, ybar), fderiv ℝ (D.g j) (xbar, ybar) d ≤ 0} := by sorry
end BilevelSOC.SecondOrder
