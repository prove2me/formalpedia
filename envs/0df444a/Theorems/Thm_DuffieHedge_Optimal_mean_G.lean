-- Prove2me | Theorems.Thm_DuffieHedge_Optimal_mean_G
-- name    : DuffieHedge.Optimal.mean_G
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:17:34.601985+00:00
-- url     : https://prove2.me/theorems/df680679-dda2-4f7c-8128-42444750fed3
-- title:
--   Proof of Lemma 2, p. 6 — $d\bar G(t)/dt=m_tE(\theta_tF_t)$
-- statement:
--   Under the standing hypotheses, let $\theta$ be a trading strategy with gain $G=G(\theta)$ and $\bar G_t=E(G_t)$. Then for almost every $t\in[0,T]$
--
--   $$\frac{d\bar G(t)}{dt}=m_tE(\theta_tF_t).$$
--
--   Precisely: $G_t$ is integrable for every $t\in[0,T]$, $\theta_tF_t$ is integrable for almost every $t\in[0,T]$, $s\mapsto m_sE(\theta_sF_s)$ is Lebesgue integrable on $[0,T]$, and $\bar G_t=\bar G_0+\int_0^tm_sE(\theta_sF_s)\,ds$ for every $t\in[0,T]$.
--
--   **Formalization Note.** Integral form of the a.e. derivative.
-- source:
--   Duffie and Richardson, Mean-Variance Hedging in Continuous Time, Ann. Appl. Probab. 1(1) (1991), §3.3, proof of Lemma 2, p. 6

import Mathlib
import Definitions.Def_DuffieHedge_Optimal_Basic

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace DuffieHedge.Optimal

/-- Proof of Lemma 2 (p. 6): for a trading strategy `θ` with gain `G = G(θ)` and
`Ḡ_t = E(G_t)`, `dḠ/dt = m_t E(θ_t F_t)` for almost every `t ∈ [0, T]`, stated in integral
form, with the expectations and the time integrand integrable. -/
theorem mean_G {Ω : Type*} [MeasurableSpace Ω] (M : Market Ω) (hM : M.Standing)
    (θ G : ℝ≥0 → Ω → ℝ) (hθ : M.IsTradingStrategy θ) (hG : M.IsGain θ G)
    (Gbar : ℝ≥0 → ℝ) (hGbar : ∀ t, Gbar t = ∫ ω, G t ω ∂M.P) :
    (∀ t ≤ M.T, Integrable (G t) M.P) ∧
    (∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) M.T)),
      Integrable (fun ω => θ s.toNNReal ω * M.F s.toNNReal ω) M.P) ∧
    IntegrableOn (fun s : ℝ =>
        M.m s.toNNReal * ∫ ω, θ s.toNNReal ω * M.F s.toNNReal ω ∂M.P)
      (Set.Icc (0 : ℝ) M.T) ∧
    ∀ t ≤ M.T, Gbar t = Gbar 0 + ∫ s in Set.Icc (0 : ℝ) t,
        M.m s.toNNReal * ∫ ω, θ s.toNNReal ω * M.F s.toNNReal ω ∂M.P := by sorry

end DuffieHedge.Optimal
