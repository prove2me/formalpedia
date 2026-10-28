-- Prove2me | Theorems.Thm_DynMomentum_ShortHorizon_proposition_3_3
-- name    : DynMomentum.ShortHorizon.proposition_3_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T12:46:43.412918+00:00
-- url     : https://prove2.me/theorems/ba268af8-707b-4ca8-b7f6-4a5b16555d10
-- title:
--   Proposition 3.3, p. 10 — for 0 ≤ T ≤ τ the optimal weight is φᴹ + φᴴ, φᴴ a weighted average of past excess returns with ω > 0 increasing then constant
-- statement:
--   Consider the momentum model $dS_t/S_t=[\alpha m_t+(1-\alpha)\mu+r]dt+\sigma dB_t$ with $m_t=\frac1\tau\int_{t-\tau}^t(dS_u/S_u-r\,du)$, parameters $0<\alpha<1$, $\sigma,\tau,\gamma>0$, $r,\mu\in\mathbb R$, and a CRRA investor with risk aversion $\gamma$ standing at time $0$ with horizon $0\le T\le\tau$. Assume the admissibility condition $D(T,0)=(\sqrt\gamma-1)e^{2\alpha T/(\sqrt\gamma\tau)}+(\sqrt\gamma+1)>0$. Let $s$ be a log-price path ($s_v=\ln S_v$) continuous on $[-\tau,0]$, and let $(A_1,A_2)$ be any solution of the first two equations of (A.9) on $[0,T]$ with $A_{1,T}=A_{2,T}=0$. Then the optimal weight of (A.11),
--   $$\phi^*_0 = \frac{\theta_0}{\gamma\sigma} + A_{1,0}s_0 + A_{2,0},\qquad \theta_0=\frac{(1-\alpha)\mu-\alpha(r-\sigma^2/2)+\frac\alpha\tau(s_0-s_{-\tau})}{\sigma},$$
--   decomposes as $\phi^*_0=\phi^M_0+\phi^H_0$ (3.8), where
--   $$\phi^M_0 = \frac{\alpha}{\gamma\sigma^2}\int_{-\tau}^0\frac1\tau\Big(\frac{dS_v}{S_v}-r\,dv\Big)+\frac{(1-\alpha)\mu}{\gamma\sigma^2},\qquad \phi^H_0 = \frac{(1-\gamma)\alpha}{\gamma\sigma^2}\int_{-\tau}^0\omega_v\Big(\frac{dS_v}{S_v}-r\,dv\Big)+C_1,$$
--   with the deterministic weight $\omega$ and the constant $C_1$ of (A.14). In addition:
--   1. if $T>0$, $\omega_v>0$ for every $v\in(-\tau,0]$;
--   2. $\omega$ is strictly increasing on $[-\tau,T-\tau]$;
--   3. $\omega$ is constant on $[T-\tau,0]$.
--
--   This is the paper's main result: the optimal momentum strategy is the myopic mean-variance weight, which depends on momentum alone, plus a hedging demand that is a differently weighted average of past excess returns, with more weight on recent returns. Two price paths with the same momentum therefore receive different optimal weights.
--
--   **Formalization Note.** (1) $\phi^*_0$ is *defined* by (A.11); the stochastic optimality argument (Lemmas 3.1–3.2, martingale method, Feynman–Kac) is not formalized. (2) $C_1$ is the (A.14) constant with both printed "$-\sigma^2/2$" deleted; the printed constant makes the identity false by a path-independent amount. (3) The integrals $\int w_v(dS_v/S_v-r\,dv)$ are read pathwise as $w_0s_0-w_{-\tau}s_{-\tau}-\int_{-\tau}^0w'_vs_v\,dv+(\frac{\sigma^2}2-r)\int_{-\tau}^0w_v\,dv$ (Itô's formula plus integration by parts), with $w'=\hat\omega\,\mathbf 1_{[-\tau,T-\tau]}$ for $w=\omega$. (4) The admissibility condition is added; it is automatic for $\gamma\ge1$. (5) Positivity of $\omega$ is stated on $(-\tau,0]$ for $T>0$, since $\omega_{-\tau}=0$ and $\omega\equiv0$ at $T=0$. (6) Time is normalized to $t=0$, as in Appendix A.2; the derivatives in (A.9) are taken within $[0,T]$.
-- source:
--   Li & Liu, Optimal Dynamic Momentum Strategies, Operations Research (2022), DOI 10.1287/opre.2021.2254, author manuscript p. 10 (PDF 10), Proposition 3.3, (3.8); proof Appendix A.2, pp. 26–28 (PDF 26–28), (A.11), (A.13), (A.14)

import Mathlib
import Definitions.Def_DynMomentum_ShortHorizon_Model

namespace DynMomentum.ShortHorizon

/-- Proposition 3.3 (Li & Liu 2022, p. 10; proof Appendix A.2, pp. 26–28), at time `t = 0` with
horizon `0 ≤ T ≤ τ`: for every solution `(A₁, A₂)` of (A.9), the optimal weight of (A.11),
`φ*₀ = θ₀/(γσ) + A₁,₀ s₀ + A₂,₀`, equals `φᴹ₀ + φᴴ₀` of (3.8), with `ω`, `C₁` of (A.14) (`C₁`
corrected: the printed formula's two `- σ²/2` are deleted) and the weighted excess-return integrals
read pathwise; moreover `ω` is positive on `(-τ, 0]` (for `T > 0`), strictly increasing on
`[-τ, T - τ]` and constant on `[T - τ, 0]`. -/
theorem proposition_3_3 (P : Params) (hP : P.Standing) (T : ℝ) (hT0 : 0 ≤ T) (hTτ : T ≤ P.τ)
    (hD : 0 < P.D T 0) (s : ℝ → ℝ) (hs : ContinuousOn s (Set.Icc (-P.τ) 0))
    (A1 A2 : ℝ → ℝ) (hA : SolvesA9 P T s A1 A2) :
    phiStar P s A1 A2 = phiM P s + phiH P T s ∧
    (0 < T → ∀ v ∈ Set.Ioc (-P.τ) 0, 0 < omega P T v) ∧
    StrictMonoOn (omega P T) (Set.Icc (-P.τ) (T - P.τ)) ∧
    ∀ v ∈ Set.Icc (T - P.τ) 0, omega P T v = omega P T (T - P.τ) := by sorry

end DynMomentum.ShortHorizon
