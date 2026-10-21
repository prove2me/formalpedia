-- Prove2me | Theorems.Thm_DynMomentum_ShortHorizon_eq_A14_omegaHat_pos
-- name    : DynMomentum.ShortHorizon.eq_A14_omegaHat_pos
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:46:33.578982+00:00
-- url     : https://prove2.me/theorems/35d819ea-de2e-46e3-b35a-3e2ab3d72dae
-- title:
--   (A.14), p. 28 — the weight density ω̂ᵤ is positive for u ∈ [−τ, −τ + T]
-- statement:
--   Let $0<\alpha<1$, $\sigma,\tau,\gamma>0$, $0\le T\le\tau$, and assume the admissibility condition $D(T,0)=(\sqrt\gamma-1)e^{2\alpha T/(\sqrt\gamma\tau)}+(\sqrt\gamma+1)>0$. With
--   $$C_{0,u} = \frac{\alpha^2\big(e^{2\alpha(T-u)/(\sqrt\gamma\tau)}+1\big)}{\gamma^{3/2}\sigma^2\tau^2\big[(\sqrt\gamma-1)e^{2\alpha(T-u)/(\sqrt\gamma\tau)}+(\sqrt\gamma+1)\big]},\qquad \hat\omega_u = \frac{\gamma\sigma^2}{\alpha}C_{0,u+\tau}\exp\Big\{\int_0^{u+\tau}\Big[\frac{\gamma(1-\gamma)\sigma^2\tau}{\alpha}C_{0,\hat u}+\frac\alpha\tau\Big]d\hat u\Big\},$$
--   one has
--   $$\hat\omega_u > 0\qquad\text{for every } u\in[-\tau,-\tau+T].$$
--
--   The density $\hat\omega$ is the rate at which the hedging weight $\omega_v=\int_{-\tau}^v\hat\omega_u\,du$ grows, so its positivity is what makes the hedging demand of Proposition 3.3 put more weight on recent returns.
--
--   **Formalization Note.** The admissibility condition is added (it is automatic for $\gamma\ge1$); without it $C_0$ has a vanishing denominator and Lean's convention $x/0=0$ would make the statement false. $\gamma^{3/2}$ is written $\gamma\sqrt\gamma$.
-- source:
--   Li & Liu, Optimal Dynamic Momentum Strategies, Operations Research (2022), DOI 10.1287/opre.2021.2254, author manuscript p. 28 (PDF 28), (A.14), proof of Proposition 3.3, Appendix A.2

import Mathlib
import Definitions.Def_DynMomentum_ShortHorizon_Model

namespace DynMomentum.ShortHorizon

/-- (A.14) (Li & Liu 2022, p. 28): under the admissibility condition `D(T, 0) > 0`, the weight
density `ω̂ᵤ` is positive for `u ∈ [-τ, -τ + T]`. -/
theorem eq_A14_omegaHat_pos (P : Params) (hP : P.Standing) (T : ℝ) (hT0 : 0 ≤ T)
    (hTτ : T ≤ P.τ) (hD : 0 < P.D T 0) :
    ∀ u ∈ Set.Icc (-P.τ) (-P.τ + T), 0 < omegaHat P T u := by sorry

end DynMomentum.ShortHorizon
