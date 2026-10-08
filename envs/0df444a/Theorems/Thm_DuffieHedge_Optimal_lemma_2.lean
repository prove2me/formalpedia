-- Prove2me | Theorems.Thm_DuffieHedge_Optimal_lemma_2
-- name    : DuffieHedge.Optimal.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:18:02.77312+00:00
-- url     : https://prove2.me/theorems/b133cfd4-1e8a-4bdc-9a06-d3499f7d5929
-- title:
--   Lemma 2 — the inner product $H_t$ of (12) solves $\dot H_t=-(m_t^2/v_t^2)H_t$ (13)
-- statement:
--   Under the standing hypotheses, let $\theta$ be an arbitrary trading strategy with gain $G(\theta)$, let $G^*$ solve (10), $\varphi=\Phi(G^*)$, and let
--
--   $$H_t=\big(L-Z_t-G^*_t\,\big|\,G(\theta)_t\big)=E\big[(L-Z_t-G^*_t)\,G(\theta)_t\big],\qquad t\in[0,T]\quad(12).$$
--
--   Then $H$ is differentiable in the sense below and
--
--   $$\dot H_t=-\frac{m_t^2}{v_t^2}H_t,\qquad t\in[0,T]\quad(13).$$
--
--   Precisely: the product $(L-Z_t-G^*_t)G(\theta)_t$ is integrable for every $t\in[0,T]$, $s\mapsto (m_s^2/v_s^2)H_s$ is Lebesgue integrable on $[0,T]$, and
--
--   $$H_t=H_0-\int_0^t\frac{m_s^2}{v_s^2}H_s\,ds\qquad\text{for every }t\in[0,T].$$
--
--   With $H_0=0$ and the solution formula for (13), this gives $H_T=0$, which is the orthogonality (8) that proves Proposition 1.
--
--   **Formalization Note.** The paper says "the derivative $\dot H_t$ is well defined" for $t\in[0,T]$; its proof establishes it "for almost every $t$" (the coefficients are only measurable). We state the integral form, which says $H$ is absolutely continuous with $\dot H_t=-(m_t^2/v_t^2)H_t$ for almost every $t$; no continuity of the coefficients is assumed.
-- source:
--   Duffie and Richardson, Mean-Variance Hedging in Continuous Time, Ann. Appl. Probab. 1(1) (1991), Lemma 2, (12)–(13), p. 5

import Mathlib
import Definitions.Def_DuffieHedge_Optimal_Basic

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace DuffieHedge.Optimal

/-- Lemma 2 (p. 5): let `θ` be a trading strategy with gain `G = G(θ)`, `G*` a solution of (10)
and `H_t = (L − Z_t − G*_t | G_t) = E[(L − Z_t − G*_t) G_t]` (12). Then `H` is absolutely
continuous on `[0, T]` with `Ḣ_t = −(m_t²/v_t²) H_t` (13) for almost every `t`, stated in
integral form: `H_t = H_0 − ∫₀ᵗ (m_s²/v_s²) H_s ds` for every `t ∈ [0, T]`. -/
theorem lemma_2 {Ω : Type*} [MeasurableSpace Ω] (M : Market Ω) (hM : M.Standing)
    (k L : ℝ) (Gs : ℝ≥0 → Ω → ℝ) (hGs : M.SolvesEq10 k L Gs)
    (θ G : ℝ≥0 → Ω → ℝ) (hθ : M.IsTradingStrategy θ) (hG : M.IsGain θ G)
    (H : ℝ≥0 → ℝ) (hH : ∀ t, H t = ∫ ω, (L - M.Z k t ω - Gs t ω) * G t ω ∂M.P) :
    (∀ t ≤ M.T, Integrable (fun ω => (L - M.Z k t ω - Gs t ω) * G t ω) M.P) ∧
    IntegrableOn (fun s : ℝ => M.m s.toNNReal ^ 2 / M.v s.toNNReal ^ 2 * H s.toNNReal)
      (Set.Icc (0 : ℝ) M.T) ∧
    ∀ t ≤ M.T, H t = H 0 - ∫ s in Set.Icc (0 : ℝ) t,
        M.m s.toNNReal ^ 2 / M.v s.toNNReal ^ 2 * H s.toNNReal := by sorry

end DuffieHedge.Optimal
