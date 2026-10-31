-- Prove2me | Theorems.Thm_FlexLearning_Threshold_VN_eq
-- name    : FlexLearning.Threshold.VN_eq
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:25:58.886087+00:00
-- url     : https://prove2.me/theorems/2925315b-9b8f-41a0-98d9-eea9f1779663
-- title:
--   Proof of Proposition 1, p. A6 — two-period non-flexible optimum: Q̄¹_N and V_N in closed form
-- statement:
--   In the two-period model with second-period demand equal to first-period demand, independent demands uniform on $[x, x+U]$ ($x \ge 0$, $U > 0$), price $p$ and dedicated unit cost $c$ with $0 \le c < p$, let $V_N = \sup_{\mathbf Q \in \mathbb R^2_+} v_N(\mathbf Q)$ be the optimal two-period profit of the non-flexible system. With $\Delta = (p-c)(p+c) + cp$, the symmetric capacity
--   $$\bar Q^1_N = x + U\,\frac{(p-c)(p+c)}{\Delta}$$
--   for each product attains $V_N$, and
--   $$V_N = 4x(p-c) + U\,\frac{(p-c)^2(3c+2p)}{\Delta}.$$
--
--   This is one side of the comparison in Proposition 1.
--
--   **Formalization Note** $U > 0$ and $0 \le c < p$ are added. The page also prints the second derivative of $v_N$; it is not part of this statement.
-- source:
--   Chod, Markakis & Trichakis, On the Learning Benefits of Resource Flexibility, SSRN preprint 3212177 (version of December 6, 2019), p. A6 (PDF 39), proof of Proposition 1

import Mathlib
import Definitions.Def_FlexLearning_Threshold_Model

namespace FlexLearning.Threshold

theorem VN_eq (p c x U : ℝ) (hc : 0 ≤ c) (hcp : c < p) (hx : 0 ≤ x) (hU : 0 < U) :
    vN p c x U (x + U * ((p - c) * (p + c) / ((p - c) * (p + c) + c * p)),
        x + U * ((p - c) * (p + c) / ((p - c) * (p + c) + c * p))) = VN p c x U ∧
    VN p c x U =
      4 * x * (p - c) + U * ((p - c) ^ 2 * (3 * c + 2 * p) / ((p - c) * (p + c) + c * p)) := by sorry

end FlexLearning.Threshold
