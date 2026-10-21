-- Prove2me | Theorems.Thm_DynMomentum_ShortHorizon_eq_A13_A1
-- name    : DynMomentum.ShortHorizon.eq_A13_A1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:46:32.546189+00:00
-- url     : https://prove2.me/theorems/ed67bda8-764e-4e32-a241-ed3fcf042520
-- title:
--   (A.13), p. 28 — the closed form of A₁,ₜ solves the Riccati equation of (A.9) with A₁,T = 0
-- statement:
--   Let $0<\alpha<1$, $\sigma,\tau,\gamma>0$ and $0\le T\le\tau$ (the setting of §3.1 and Appendix A.2), and write $E_T(t)=e^{2\alpha(T-t)/(\sqrt\gamma\,\tau)}$ and $D(T,t)=(\sqrt\gamma-1)E_T(t)+(\sqrt\gamma+1)$. Assume the **admissibility condition** $D(T,0)>0$. Then
--   $$A_{1,t} = \frac{\alpha(\gamma-1)\big(1-E_T(t)\big)}{\gamma\sigma^2\tau\,D(T,t)}$$
--   satisfies, for every $t\in[0,T]$, the Riccati equation of (A.9),
--   $$\dot A_{1,t} = -\sigma^2A_{1,t}^2 - \frac{2\alpha}{\gamma\tau}A_{1,t} - \frac{1-\gamma}{\gamma^2}\frac{\alpha^2}{\tau^2\sigma^2},$$
--   and $A_{1,T}=0$.
--
--   This exhibits the solution of the first equation of (A.9), on which the hedging weights $\omega$ of (A.14) are built.
--
--   **Formalization Note.** The derivative is taken within $[0,T]$. The admissibility condition is not on the page: for $\gamma\ge1$ it holds automatically, but for small $\gamma<1$ the denominator vanishes inside $[0,T]$ and the Riccati solution blows up. Since $D(T,\cdot)$ is monotone, $D(T,0)>0$ gives $D>0$ on all of $[0,T]$.
-- source:
--   Li & Liu, Optimal Dynamic Momentum Strategies, Operations Research (2022), DOI 10.1287/opre.2021.2254, author manuscript p. 28 (PDF 28), (A.13) first line, proof of Proposition 3.3, Appendix A.2

import Mathlib
import Definitions.Def_DynMomentum_ShortHorizon_Model

namespace DynMomentum.ShortHorizon

/-- (A.13), first line (Li & Liu 2022, p. 28): under the admissibility condition `D(T, 0) > 0`,
for `0 ≤ T ≤ τ`, `A₁,ₜ = α(γ - 1)(1 - e^{2α(T-t)/(√γ τ)}) / (γσ²τ[(√γ - 1)e^{2α(T-t)/(√γ τ)} + (√γ + 1)])`
solves the Riccati equation of (A.9) on `[0, T]` with `A₁,T = 0`. -/
theorem eq_A13_A1 (P : Params) (hP : P.Standing) (T : ℝ) (hT0 : 0 ≤ T) (hTτ : T ≤ P.τ)
    (hD : 0 < P.D T 0) :
    (∀ u ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt
        (fun t => P.α * (P.γ - 1) * (1 - P.expo T t) / (P.γ * P.σ ^ 2 * P.τ * P.D T t))
        (rhs1 P (P.α * (P.γ - 1) * (1 - P.expo T u) / (P.γ * P.σ ^ 2 * P.τ * P.D T u)))
        (Set.Icc 0 T) u) ∧
    P.α * (P.γ - 1) * (1 - P.expo T T) / (P.γ * P.σ ^ 2 * P.τ * P.D T T) = 0 := by sorry

end DynMomentum.ShortHorizon
