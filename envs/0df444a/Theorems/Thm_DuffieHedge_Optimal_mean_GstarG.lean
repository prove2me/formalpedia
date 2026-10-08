-- Prove2me | Theorems.Thm_DuffieHedge_Optimal_mean_GstarG
-- name    : DuffieHedge.Optimal.mean_GstarG
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:17:33.37798+00:00
-- url     : https://prove2.me/theorems/7d9e8596-bdf3-48f9-838d-5a58802f83f5
-- title:
--   Proof of Lemma 2, p. 6 — the mean $\bar Y$ of $Y=G^*G(\theta)$
-- statement:
--   Under the standing hypotheses, let $G^*$ solve (10), $\varphi=\Phi(G^*)$, and let $\theta$ be a trading strategy with gain $G=G(\theta)$. Let $Y_t=G^*_tG_t$ and $\bar Y_t=E(Y_t)$. Then for almost every $t\in[0,T]$
--
--   $$\frac{d\bar Y(t)}{dt}=m_tE(\varphi_tF_tG_t)+m_tE(\theta_tF_tG^*_t)+v_t^2E(\varphi_t\theta_tF_t^2).$$
--
--   Precisely: $G^*_tG_t$ is integrable for every $t\in[0,T]$, the three products inside the expectations are integrable for almost every $t\in[0,T]$, the right-hand side is Lebesgue integrable on $[0,T]$, and $\bar Y_t=\bar Y_0+\int_0^t(\text{right-hand side at }s)\,ds$ for every $t\in[0,T]$.
--
--   **Formalization Note.** Integral form of the a.e. derivative, as in the companion statement for $\bar X$.
-- source:
--   Duffie and Richardson, Mean-Variance Hedging in Continuous Time, Ann. Appl. Probab. 1(1) (1991), §3.3, proof of Lemma 2, p. 6

import Mathlib
import Definitions.Def_DuffieHedge_Optimal_Basic

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace DuffieHedge.Optimal

/-- Proof of Lemma 2 (p. 6): with `G*` a solution of (10), `φ = Φ(G*)`, `θ` a trading strategy
with gain `G = G(θ)`, `Y_t = G*_t G_t` and `Ȳ_t = E(Y_t)`, for almost every `t ∈ [0, T]`
`dȲ/dt = m_t E(φ_t F_t G_t) + m_t E(θ_t F_t G*_t) + v_t² E(φ_t θ_t F_t²)`,
stated in integral form, with the expectations and the time integrand integrable. -/
theorem mean_GstarG {Ω : Type*} [MeasurableSpace Ω] (M : Market Ω) (hM : M.Standing)
    (k L : ℝ) (Gs : ℝ≥0 → Ω → ℝ) (hGs : M.SolvesEq10 k L Gs)
    (θ G : ℝ≥0 → Ω → ℝ) (hθ : M.IsTradingStrategy θ) (hG : M.IsGain θ G)
    (Ybar : ℝ≥0 → ℝ) (hYbar : ∀ t, Ybar t = ∫ ω, Gs t ω * G t ω ∂M.P) :
    (∀ t ≤ M.T, Integrable (fun ω => Gs t ω * G t ω) M.P) ∧
    (∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) M.T)),
      Integrable (fun ω => M.feedback k L Gs s.toNNReal ω * M.F s.toNNReal ω
        * G s.toNNReal ω) M.P ∧
      Integrable (fun ω => θ s.toNNReal ω * M.F s.toNNReal ω * Gs s.toNNReal ω) M.P ∧
      Integrable (fun ω => M.feedback k L Gs s.toNNReal ω * θ s.toNNReal ω
        * M.F s.toNNReal ω ^ 2) M.P) ∧
    IntegrableOn (fun s : ℝ =>
        M.m s.toNNReal * ∫ ω, M.feedback k L Gs s.toNNReal ω * M.F s.toNNReal ω
          * G s.toNNReal ω ∂M.P
        + M.m s.toNNReal * ∫ ω, θ s.toNNReal ω * M.F s.toNNReal ω * Gs s.toNNReal ω ∂M.P
        + M.v s.toNNReal ^ 2 * ∫ ω, M.feedback k L Gs s.toNNReal ω * θ s.toNNReal ω
          * M.F s.toNNReal ω ^ 2 ∂M.P)
      (Set.Icc (0 : ℝ) M.T) ∧
    ∀ t ≤ M.T, Ybar t = Ybar 0 + ∫ s in Set.Icc (0 : ℝ) t,
        (M.m s.toNNReal * ∫ ω, M.feedback k L Gs s.toNNReal ω * M.F s.toNNReal ω
          * G s.toNNReal ω ∂M.P
        + M.m s.toNNReal * ∫ ω, θ s.toNNReal ω * M.F s.toNNReal ω * Gs s.toNNReal ω ∂M.P
        + M.v s.toNNReal ^ 2 * ∫ ω, M.feedback k L Gs s.toNNReal ω * θ s.toNNReal ω
          * M.F s.toNNReal ω ^ 2 ∂M.P) := by sorry

end DuffieHedge.Optimal
