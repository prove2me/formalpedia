-- Prove2me | Theorems.Thm_AggDiscountStopping_OneBarrier_prop_4_7_boundary_limits
-- name    : AggDiscountStopping.OneBarrier.prop_4_7_boundary_limits
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T03:56:11.633146+00:00
-- url     : https://prove2.me/theorems/eb5d9b5f-b59c-4b4f-9302-dbb55ec8b08f
-- title:
--   Proof of Proposition 4.7, display on p. 14 — under I₁ = I₂ = +∞ and r > 0, φ_r(x) → 0 and φ′_r(x)exp(∫_ε^x 2µ/σ²) → 0
-- statement:
--   Assume the standing assumptions of §4 and Conditions C-(i), C-(ii)-1 and C-(ii)-2 for a fixed $\epsilon>0$ (so $I_1=I_2=+\infty$). Let $r>0$ and let $\psi$ be a positive, decreasing, $C^2$ solution on $(0,\infty)$ of $\tfrac12\sigma^2\psi''+\mu\psi'=r\psi$. Then, as $x\to+\infty$,
--   $$\psi(x)\to0\qquad\text{and}\qquad\psi'(x)\exp\Big(\int_\epsilon^x\frac{2\mu(y)}{\sigma^2(y)}dy\Big)\to0.$$
--
--   This is the behaviour of the decreasing solution at a natural boundary, which the paper takes from Cecchi et al. (1989, Theorems 2 and 3). It is what shows $a(x)f(x)\to0$ in the proof of Proposition 4.7.
--
--   **Formalization Note** The statement is posed for $r>0$ only. At $r=0$ a positive constant solves (4.1), and it does not tend to $0$; the proof of Proposition 4.7 needs the limits only for the larger of the two rates, which is positive.
-- source:
--   Deng, Yu, Zhang, On time-consistent equilibrium stopping under aggregation of diverse discount rates, arXiv:2302.07470v4, proof of Proposition 4.7, display on p. 14 (Cecchi et al. 1989, Theorems 2 & 3)

import Mathlib
import Definitions.Def_AggDiscountStopping_OneBarrier_Setting

open MeasureTheory Set Filter Topology
open scoped NNReal

namespace AggDiscountStopping.OneBarrier

theorem prop_4_7_boundary_limits (M : Model) (hM : M.Valid) (hCi : M.CondI)
    (hCii1 : M.CondII1) (ε : ℝ) (hε : 0 < ε) (hCii2 : M.CondII2 ε)
    (r : ℝ) (hr : 0 < r) (ψ : ℝ → ℝ) (hψ : IsDecreasingSolution M r ψ) :
    Tendsto ψ atTop (𝓝 0) ∧
      Tendsto (fun x => deriv ψ x * Real.exp (∫ y in ε..x, 2 * M.μ y / M.σ y ^ 2))
        atTop (𝓝 0) := by sorry

end AggDiscountStopping.OneBarrier
