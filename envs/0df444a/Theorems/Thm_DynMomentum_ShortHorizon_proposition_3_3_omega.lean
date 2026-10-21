-- Prove2me | Theorems.Thm_DynMomentum_ShortHorizon_proposition_3_3_omega
-- name    : DynMomentum.ShortHorizon.proposition_3_3_omega
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:46:35.804293+00:00
-- url     : https://prove2.me/theorems/11202526-8387-40cc-b9b5-03efc4204947
-- title:
--   Proposition 3.3, p. 10 — ωᵥ is positive, increasing on [−τ, T − τ] and constant on [T − τ, 0]
-- statement:
--   Let $0<\alpha<1$, $\sigma,\tau,\gamma>0$, $0\le T\le\tau$, and assume the admissibility condition $D(T,0)=(\sqrt\gamma-1)e^{2\alpha T/(\sqrt\gamma\tau)}+(\sqrt\gamma+1)>0$. Let $\omega$ be the hedging weight of (A.14),
--   $$\omega_v = \begin{cases}\int_{-\tau}^{v}\hat\omega_u\,du, & v\in[-\tau,-\tau+T],\\ \int_{-\tau}^{-\tau+T}\hat\omega_u\,du, & v\in[-\tau+T,0].\end{cases}$$
--   Then, with the investor at time $t=0$:
--   1. if $T>0$, then $\omega_v>0$ for every $v\in(-\tau,0]$;
--   2. $\omega$ is strictly increasing on $[-\tau,T-\tau]$;
--   3. $\omega$ is constant on $[T-\tau,0]$: $\omega_v=\omega_{T-\tau}$ there.
--
--   This is the last sentence of Proposition 3.3: the hedging demand weights recent excess returns more heavily, up to the point $T-\tau$ beyond which all returns carry the same weight.
--
--   **Formalization Note.** The paper says "$\omega_v$ is positive" without qualification; this fails at $v=-\tau$ (where $\omega=0$) and for $T=0$ (where $\omega\equiv0$), so positivity is stated on $(-\tau,0]$ under $T>0$. "Increases" is stated strictly, as $\hat\omega>0$ gives. Time is normalized to $t=0$; the model is time-homogeneous.
-- source:
--   Li & Liu, Optimal Dynamic Momentum Strategies, Operations Research (2022), DOI 10.1287/opre.2021.2254, author manuscript p. 10 (PDF 10), Proposition 3.3 (last sentence); ω from (A.14), p. 28

import Mathlib
import Definitions.Def_DynMomentum_ShortHorizon_Model

namespace DynMomentum.ShortHorizon

/-- Proposition 3.3, last sentence (Li & Liu 2022, p. 10), at time `t = 0`: `ωᵥ` is positive on
`(-τ, 0]` when `T > 0` (at `v = -τ`, and for `T = 0`, `ω = 0`), strictly increasing on `[-τ, T - τ]`
and constant on `[T - τ, 0]`. -/
theorem proposition_3_3_omega (P : Params) (hP : P.Standing) (T : ℝ) (hT0 : 0 ≤ T)
    (hTτ : T ≤ P.τ) (hD : 0 < P.D T 0) :
    (0 < T → ∀ v ∈ Set.Ioc (-P.τ) 0, 0 < omega P T v) ∧
    StrictMonoOn (omega P T) (Set.Icc (-P.τ) (T - P.τ)) ∧
    ∀ v ∈ Set.Icc (T - P.τ) 0, omega P T v = omega P T (T - P.τ) := by sorry

end DynMomentum.ShortHorizon
