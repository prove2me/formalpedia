-- Prove2me | Theorems.Thm_DynMomentum_ShortHorizon_eq_A13_A2
-- name    : DynMomentum.ShortHorizon.eq_A13_A2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T12:46:27.073103+00:00
-- url     : https://prove2.me/theorems/f1c8695a-5c41-4fd0-be8f-51e2bef23cdf
-- title:
--   (A.13), p. 28 — the variation-of-constants integral A₂,ₜ solves the second equation of (A.9) with A₂,T = 0
-- statement:
--   Let $0<\alpha<1$, $\sigma,\tau,\gamma>0$, $0\le T\le\tau$, and let $s$ be a log-price path continuous on $[-\tau,0]$ (so $s_{u-\tau}=\ln S_{u-\tau}$ is the realized past log price). Let $A_1$ be any solution on $[0,T]$ of the Riccati equation $\dot A_1 = -\sigma^2A_1^2-\frac{2\alpha}{\gamma\tau}A_1-\frac{1-\gamma}{\gamma^2}\frac{\alpha^2}{\tau^2\sigma^2}$. Define
--   $$A_{2,t} = \int_t^T e^{\int_t^u(\sigma^2A_{1,v}+\frac{\alpha}{\gamma\tau})dv}\Big[\Big(\Big(r-\frac{\sigma^2}2\Big)\Big(1-\frac\alpha\gamma\Big)+(1-\alpha)\frac\mu\gamma-\frac{\alpha}{\gamma\tau}s_{u-\tau}\Big)A_{1,u} + \frac{1-\gamma}{\gamma^2}\frac{\alpha}{\sigma^2\tau}\Big((1-\alpha)\mu-\alpha\Big(r-\frac{\sigma^2}2\Big)-\frac\alpha\tau s_{u-\tau}\Big)\Big]du.$$
--   Then $A_2$ satisfies, for every $t\in[0,T]$, the second equation of (A.9),
--   $$\dot A_{2,t} = -\Big(\sigma^2A_{1,t}+\frac{\alpha}{\gamma\tau}\Big)A_{2,t} - \Big[(1-\alpha)\frac\mu\gamma+\Big(r-\frac{\sigma^2}2\Big)\Big(1-\frac\alpha\gamma\Big)-\frac{\alpha}{\gamma\tau}s_{t-\tau}\Big]A_{1,t} - \frac{1-\gamma}{\gamma^2}\frac{\alpha}{\sigma^2\tau}\Big[(1-\alpha)\mu+\alpha\Big(\frac{\sigma^2}2-r\Big)-\frac\alpha\tau s_{t-\tau}\Big],$$
--   and $A_{2,T}=0$.
--
--   This is the formula through which the realized price path enters the optimal weight; the path is only continuous, so $A_2$ is differentiable although $s$ need not be.
--
--   **Formalization Note.** Derivatives are taken within $[0,T]$. Integrals are Mathlib interval integrals; their integrands are continuous on $[0,T]$ because $A_1$ is differentiable there and $u-\tau\in[-\tau,0]$.
-- source:
--   Li & Liu, Optimal Dynamic Momentum Strategies, Operations Research (2022), DOI 10.1287/opre.2021.2254, author manuscript p. 28 (PDF 28), (A.13) second line, proof of Proposition 3.3, Appendix A.2

import Mathlib
import Definitions.Def_DynMomentum_ShortHorizon_Model

namespace DynMomentum.ShortHorizon

/-- (A.13), second line (Li & Liu 2022, p. 28): for any solution `A₁` of the first ODE of (A.9) on
`[0, T]`, the variation-of-constants integral
`A₂,ₜ = ∫ₜᵀ e^{∫ₜᵘ (σ² A₁,ᵥ + α/(γτ)) dv} [(...) A₁,ᵤ + ((1-γ)/γ²)(α/(σ²τ))(...)] du`,
with `ln S_{u-τ} = s (u - τ)`, solves the second ODE of (A.9) on `[0, T]` with `A₂,T = 0`. -/
theorem eq_A13_A2 (P : Params) (hP : P.Standing) (T : ℝ) (hT0 : 0 ≤ T) (hTτ : T ≤ P.τ)
    (s : ℝ → ℝ) (hs : ContinuousOn s (Set.Icc (-P.τ) 0)) (A1 : ℝ → ℝ)
    (hA1 : ∀ u ∈ Set.Icc (0 : ℝ) T, HasDerivWithinAt A1 (rhs1 P (A1 u)) (Set.Icc 0 T) u) :
    let A2 : ℝ → ℝ := fun t => ∫ u in t..T,
      Real.exp (∫ v in t..u, (P.σ ^ 2 * A1 v + P.α / (P.γ * P.τ)))
        * (((P.r - P.σ ^ 2 / 2) * (1 - P.α / P.γ) + (1 - P.α) * P.μ / P.γ
              - P.α / (P.γ * P.τ) * s (u - P.τ)) * A1 u
          + (1 - P.γ) / P.γ ^ 2 * (P.α / (P.σ ^ 2 * P.τ))
              * ((1 - P.α) * P.μ - P.α * (P.r - P.σ ^ 2 / 2) - P.α / P.τ * s (u - P.τ)))
    (∀ t ∈ Set.Icc (0 : ℝ) T, HasDerivWithinAt A2 (rhs2 P s t (A1 t) (A2 t)) (Set.Icc 0 T) t) ∧
      A2 T = 0 := by sorry

end DynMomentum.ShortHorizon
