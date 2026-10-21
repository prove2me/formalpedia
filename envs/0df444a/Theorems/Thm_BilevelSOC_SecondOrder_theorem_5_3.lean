-- Prove2me | Theorems.Thm_BilevelSOC_SecondOrder_theorem_5_3
-- name    : BilevelSOC.SecondOrder.theorem_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:48:03.652144+00:00
-- url     : https://prove2.me/theorems/bfce0970-8d1b-487f-8cb2-af47002a7718
-- title:
--   Theorem 5.3 — second-order sufficient condition for bilevel growth
-- statement:
--   Let $(\bar x,\bar y)$ be feasible for the optimistic bilevel program. Assume ACQ for the lower-level constraint set (5.2), local Lipschitz continuity and second-order directional differentiability of the value function $\varphi$ at $\bar x$, and second-order epi-regularity of $-\varphi$. Assume also the first-order condition (5.4) on $L_M^\varphi$ and positive optimal value of the minimax program (5.5) for every nonzero direction in $C_M^\varphi$. Then there are a neighbourhood $U$ and $C>0$ such that
--   $$F(x,y)\ge F(\bar x,\bar y)+C\bigl(\|x-\bar x\|_2^2+\|y-\bar y\|_2^2\bigr)\qquad((x,y)\in M\cap U),$$
--   and $(\bar x,\bar y)$ is a strict local minimizer of the bilevel program. The condition controls all nearby bilevel-feasible pairs.
--
--   **Formalization Note** The data satisfy the paper's standing $C^2$ assumption. The real local representative of $\varphi$ agrees with the extended-real infimum near $\bar x$; second-order derivative values are finite. The minimax positivity is a uniform bound over all $w$.
-- source:
--   Mehlitz & Zemkoho, Sufficient Optimality Conditions in Bilevel Programming, arXiv:1911.01647v1, pp. 19–20, Theorem 5.3

import Definitions.Def_BilevelSOC_SecondOrder_Model
open scoped Topology

namespace BilevelSOC.SecondOrder
theorem theorem_5_3 {n m p q : ℕ} (D : Data n m p q) (hD : Standing D)
    (xbar : E n) (ybar : Y m) (hfeas : (xbar, ybar) ∈ feasSet D)
    (hACQ : ACQ52 D (xbar, ybar))
    (φr : E n → ℝ) (U : Set (E n)) (hU : U ∈ 𝓝 xbar)
    (hφU : ∀ x ∈ U, valueFn D x = (φr x : EReal))
    (L : NNReal) (hLip : LipschitzOnWith L φr U)
    (φ' : E n → ℝ) (φ'' : E n → E n → ℝ)
    (hφ2 : SecondOrderDirDiff φr xbar φ' φ'')
    (hepi : SecondOrderEpiRegular (fun x => -φr x) xbar
      (fun d => -φ' d) (fun d w => -φ'' d w))
    (h54 : ∀ d ∈ linConeVF D (xbar, ybar) φ',
      0 ≤ fderiv ℝ D.F (xbar, ybar) d)
    (h55 : ∀ d ∈ critConeVF D (xbar, ybar) φ',
      d ≠ 0 → Prog55Pos D (xbar, ybar) φ'' d) :
    (∃ W : Set (E n × Y m), W ∈ 𝓝 (xbar, ybar) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ z ∈ feasSet D ∩ W,
        D.F (xbar, ybar) +
          C * (‖z.1 - xbar‖ ^ 2 + ‖z.2 - ybar‖ ^ 2) ≤ D.F z) ∧
    (∃ W : Set (E n × Y m), W ∈ 𝓝 (xbar, ybar) ∧
      ∀ z ∈ feasSet D ∩ W, z ≠ (xbar, ybar) → D.F (xbar, ybar) < D.F z) := by sorry
end BilevelSOC.SecondOrder
