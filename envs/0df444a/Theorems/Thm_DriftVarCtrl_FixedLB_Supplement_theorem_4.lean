-- Prove2me | Theorems.Thm_DriftVarCtrl_FixedLB_Supplement_theorem_4
-- name    : DriftVarCtrl.FixedLB.Supplement.theorem_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T10:47:28.315188+00:00
-- url     : https://prove2.me/theorems/97745588-70d2-4032-9133-ff7e93ba1bfc
-- title:
--   Theorem 4, pp. 20–22 — free lower boundary: 'use 1, stop', 'use 2, stop' or 'use 1 then 2, stop' is optimal under (25), (26), (27)
-- statement:
--   Consider the free-lower-boundary problem with $v_1<v_2$. Let $\hat h_2(h_1)=\frac{\mu_2}{\mu_1}h_1\Bigl[1+\frac{v_2-v_1}{v_2}LW\bigl(-e^{-1-\frac{(-M)\mu_1v_1}{h_1}}\bigr)\Bigr]$, where $LW$ is the principal branch of the Lambert W function on $[-1/e,\infty)$; its argument lies in that domain. Define the conditions
--   $$\text{(25) } h_2>\hat h_2(h_1),\qquad \text{(26) } h_2<\frac{\sigma_2^2}{\sigma_1^2}h_1,\qquad \text{(27) } \frac{\sigma_2^2}{\sigma_1^2}h_1<h_2<\hat h_2(h_1).$$
--
--   1. If (25) holds, there is $\tilde U>0$ such that the policy using control 1 on $[U-\tilde U,U)$ and stopping on $(-\infty,U-\tilde U)$ is optimal.
--   2. If (26) holds, there is $\tilde U>0$ such that the policy using control 2 on $[U-\tilde U,U)$ and stopping on $(-\infty,U-\tilde U)$ is optimal.
--   3. If (27) holds, there are $\tilde U>S^*>0$ such that the policy using control 1 on $[U-\tilde U,U-\tilde U+S^*)$, control 2 on $[U-\tilde U+S^*,U)$ and stopping on $(-\infty,U-\tilde U)$ is optimal.
--
--   With a free lower boundary the optimal policy is at most two-interval and never "use 2 then 1"; the stopping level $U-\tilde U$ may be above or below $0$.
--
--   **Formalization Note** Optimality is over every stopping interval policy (every stopping level, every number of intervals) with the analytic value of the definition `FreeModel`; $\tilde U$ may exceed $U$. The standing $v_1<v_2$ of p. 12 is a hypothesis.
--
--   Differences from the source:
--
--   - encoding: the value of a policy is the expected cost (112) of the controlled diffusion → the analytic value IsStopValue: zero at and below the stopping level z₀, C¹ on [z₀, U], equal to M at U, and on each open piece C² and solving hᵢ + μᵢW′ + σᵢ²/2·W″ = 0; reason: Mathlib has no stochastic integral; this is the boundary-value system (115), (143)–(144), (162)–(167) the paper itself writes for every policy, as in the base mission's IsValue
--   - encoding: LW is the Lambert W function on [−1/e, ∞) → LiquidWelfareFPA.lambertW, the principal branch (the unique y ≥ −1 with ye^y = x), with the value 0 below −1/e; reason: the argument −e^{−1−(−M)μ₁v₁/h₁} lies in (−1/e, 0) for h₁ > 0, so the junk value is never evaluated
--   - encoding: stopping on (−∞, U − Ũ) and using the control on [U − Ũ, U) → the stopping policy with z₀ = U − Ũ, whose value vanishes at and below z₀; reason: Definition 5 stops when X ≤ z₀; the level itself is absorbing and carries the value 0 either way
-- source:
--   Wang, Zenios, New Venture Creation: A Drift-Variance Diffusion Control Model, SSRN 3667132 (working paper, sha256 2d7a57ba…), pp. 20–22, Theorem 4, (25)–(27) (proof pp. EC-23–EC-27)

import Mathlib
import Definitions.Def_DriftVarCtrl_FixedLB_Model
import Definitions.Def_DriftVarCtrl_FixedLB_Supplement_FreeModel
import Definitions.Def_DriftVarCtrl_FixedLB_Supplement_Thresholds

namespace DriftVarCtrl.FixedLB.Supplement

open DriftVarCtrl.FixedLB

/-- Theorem 4 (Wang, Zenios, New Venture Creation: A Drift-Variance Diffusion Control Model, SSRN 3667132 (working paper, sha256 2d7a57ba…), pp. 20–22, (25)–(27); proof pp. EC-23–EC-27). With a free lower boundary:
(a) if `h₂ > ĥ₂(h₁)` (25), there is `Ũ > 0` such that using control 1 on `[U − Ũ, U)` and
stopping on `(−∞, U − Ũ)` is optimal; (b) if `h₂ < (σ₂²/σ₁²) h₁` (26), there is `Ũ > 0` such that
using control 2 on `[U − Ũ, U)` and stopping below is optimal; (c) if
`(σ₂²/σ₁²) h₁ < h₂ < ĥ₂(h₁)` (27), there are `Ũ > S* > 0` such that using control 1 on
`[U − Ũ, U − Ũ + S*)`, control 2 on `[U − Ũ + S*, U)` and stopping below is optimal. Here
`ĥ₂(h₁) = (μ₂/μ₁) h₁ [1 + ((v₂ − v₁)/v₂) LW(−e^{−1−(−M)μ₁v₁/h₁})]` with `LW` the principal branch
of the Lambert W function.

Formalization Note: optimality is `IsStopOptimal`, over every stopping interval policy (every
stopping level, every number of intervals) with the analytic value `IsStopValue`; `Ũ` may exceed
`U` (stopping level below `0`). The standing `v₁ < v₂` (p. 12) is `hv`. -/
theorem theorem_4 (p : Params) (hv : v p .one < v p .two) :
    (cond25 p → ∃ (Ũ : ℝ) (hŨ : 0 < Ũ),
      IsStopOptimal p (stopOne p .one (p.U - Ũ) (by linarith))) ∧
    (cond26 p → ∃ (Ũ : ℝ) (hŨ : 0 < Ũ),
      IsStopOptimal p (stopOne p .two (p.U - Ũ) (by linarith))) ∧
    (cond27 p → ∃ (Ũ S : ℝ) (hS : 0 < S) (hSŨ : S < Ũ),
      IsStopOptimal p (stopOneTwo p (p.U - Ũ) (p.U - Ũ + S) (by linarith) (by linarith))) := by sorry

end DriftVarCtrl.FixedLB.Supplement
