-- Prove2me | Theorems.Thm_DuffieHedge_Optimal_mean_ZG
-- name    : DuffieHedge.Optimal.mean_ZG
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:17:13.448719+00:00
-- url     : https://prove2.me/theorems/6758d8d7-e3bb-4c2e-bfe7-d70cf9722713
-- title:
--   Proof of Lemma 2, p. 5 — the mean $\bar X$ of $X=ZG(\theta)$
-- statement:
--   Under the standing hypotheses, let $\theta$ be a trading strategy with gain $G=G(\theta)$, let $X_t=Z_tG_t$ and $\bar X_t=E(X_t)$. Then for almost every $t\in[0,T]$
--
--   $$\frac{d\bar X(t)}{dt}=(\gamma_t+\mu_t)E[Z_tG_t]+m_tE[Z_t\theta_tF_t]+\sigma_tv_t\rho_tE[Z_t\theta_tF_t].$$
--
--   Precisely: $Z_tG_t$ is integrable for every $t\in[0,T]$, $Z_t\theta_tF_t$ is integrable for almost every $t\in[0,T]$, the right-hand side is Lebesgue integrable on $[0,T]$, and $\bar X_t=\bar X_0+\int_0^t(\text{right-hand side at }s)\,ds$ for every $t\in[0,T]$.
--
--   This is one of three moment computations whose combination gives the ODE (13) of Lemma 2.
--
--   **Formalization Note.** "For almost every $t$, $d\bar X/dt=\dots$" is stated in its integral form, which is equivalent to it together with the absolute continuity of $\bar X$ that the proof uses.
-- source:
--   Duffie and Richardson, Mean-Variance Hedging in Continuous Time, Ann. Appl. Probab. 1(1) (1991), §3.3, proof of Lemma 2, p. 5

import Mathlib
import Definitions.Def_DuffieHedge_Optimal_Basic

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace DuffieHedge.Optimal

/-- Proof of Lemma 2 (p. 5): for a trading strategy `θ` with gain `G = G(θ)`, `X_t = Z_t G_t`
and `X̄_t = E(X_t)`, for almost every `t ∈ [0, T]`
`dX̄/dt = (γ_t + μ_t) E[Z_t G_t] + m_t E[Z_t θ_t F_t] + σ_t v_t ρ_t E[Z_t θ_t F_t]`,
stated in integral form: `X̄_t = X̄_0 + ∫₀ᵗ (…) ds` for all `t ∈ [0, T]`, with the
expectations and the time integrand integrable. -/
theorem mean_ZG {Ω : Type*} [MeasurableSpace Ω] (M : Market Ω) (hM : M.Standing) (k : ℝ)
    (θ G : ℝ≥0 → Ω → ℝ) (hθ : M.IsTradingStrategy θ) (hG : M.IsGain θ G)
    (Xbar : ℝ≥0 → ℝ) (hXbar : ∀ t, Xbar t = ∫ ω, M.Z k t ω * G t ω ∂M.P) :
    (∀ t ≤ M.T, Integrable (fun ω => M.Z k t ω * G t ω) M.P) ∧
    (∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) M.T)),
      Integrable (fun ω => M.Z k s.toNNReal ω * θ s.toNNReal ω * M.F s.toNNReal ω) M.P) ∧
    IntegrableOn (fun s : ℝ =>
        (M.γ s.toNNReal + M.μ s.toNNReal) * Xbar s.toNNReal
        + M.m s.toNNReal *
            ∫ ω, M.Z k s.toNNReal ω * θ s.toNNReal ω * M.F s.toNNReal ω ∂M.P
        + M.σ s.toNNReal * M.v s.toNNReal * M.ρ s.toNNReal *
            ∫ ω, M.Z k s.toNNReal ω * θ s.toNNReal ω * M.F s.toNNReal ω ∂M.P)
      (Set.Icc (0 : ℝ) M.T) ∧
    ∀ t ≤ M.T, Xbar t = Xbar 0 + ∫ s in Set.Icc (0 : ℝ) t,
        ((M.γ s.toNNReal + M.μ s.toNNReal) * Xbar s.toNNReal
        + M.m s.toNNReal *
            ∫ ω, M.Z k s.toNNReal ω * θ s.toNNReal ω * M.F s.toNNReal ω ∂M.P
        + M.σ s.toNNReal * M.v s.toNNReal * M.ρ s.toNNReal *
            ∫ ω, M.Z k s.toNNReal ω * θ s.toNNReal ω * M.F s.toNNReal ω ∂M.P) := by sorry

end DuffieHedge.Optimal
