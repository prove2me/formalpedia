-- Prove2me | Theorems.Thm_AggDiscountStopping_OneBarrier_proposition_4_7
-- name    : AggDiscountStopping.OneBarrier.proposition_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T03:56:03.163202+00:00
-- url     : https://prove2.me/theorems/3060ef42-3f6a-48be-9b47-b5d2ca1b566b
-- title:
--   Proposition 4.7, p. 13 — under C-(ii), r ↦ m̃_r(x) is increasing for every x > 0
-- statement:
--   Assume the standing assumptions of §4 and Conditions C-(i), C-(ii)-1 and C-(ii)-2 for a fixed $\epsilon>0$. Let $(\varphi_r)_{r\ge0}$ be a family such that each $\varphi_r$ is a positive, decreasing, $C^2$ solution on $(0,\infty)$ of $\tfrac12\sigma^2\varphi''+\mu\varphi'=r\varphi$, and put $\tilde m_r=-\varphi_r'/\varphi_r$. Then for every $x>0$ the map
--   $$r\longmapsto\tilde m_r(x)$$
--   is increasing (non-decreasing) on $[0,\infty)$: $\tilde m_{r_1}(x)\ge\tilde m_{r_2}(x)$ whenever $r_1>r_2\ge0$.
--
--   This is condition (b″) of Remark 4.3, equivalent to Condition (b) of Proposition 4.2; it drives the Harris–FKG step in the proof of Theorem 4.8.
--
--   **Formalization Note** Posed in the (b″) form to which the paper's proof reduces it, for $x>0$ (printed $x\ge0$; $\varphi_r(0)$ may be infinite). The family $\varphi$ is arbitrary among positive decreasing solutions, including at $r=0$. The printed $c(x)=2r_1(x)/\sigma^2(x)$ in the proof is a misprint for $2(r_1-r_2)/\sigma^2(x)$ and does not affect the statement. C-(i) is the standing condition of §4.
-- source:
--   Deng, Yu, Zhang, On time-consistent equilibrium stopping under aggregation of diverse discount rates, arXiv:2302.07470v4, Proposition 4.7, p. 13 (with (b′′) of Remark 4.3, p. 11)

import Mathlib
import Definitions.Def_AggDiscountStopping_OneBarrier_Setting

open MeasureTheory Set Filter Topology
open scoped NNReal

namespace AggDiscountStopping.OneBarrier

theorem proposition_4_7 (M : Model) (hM : M.Valid) (hCi : M.CondI) (hCii1 : M.CondII1)
    (ε : ℝ) (hε : 0 < ε) (hCii2 : M.CondII2 ε) (φ : ℝ → ℝ → ℝ)
    (hφ : ∀ r, 0 ≤ r → IsDecreasingSolution M r (φ r)) :
    ∀ x, 0 < x → MonotoneOn (fun r => mtilde (φ r) x) (Ici 0) := by sorry

end AggDiscountStopping.OneBarrier
