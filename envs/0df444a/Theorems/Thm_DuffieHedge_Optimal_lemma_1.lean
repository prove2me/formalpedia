-- Prove2me | Theorems.Thm_DuffieHedge_Optimal_lemma_1
-- name    : DuffieHedge.Optimal.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:16:59.969908+00:00
-- url     : https://prove2.me/theorems/93428531-5762-4749-a7c5-5ade65696640
-- title:
--   Lemma 1 — a trading strategy is optimal for (3) iff its terminal error is orthogonal to every terminal gain
-- statement:
--   Work in the futures-hedging market of Duffie and Richardson under the standing hypotheses, with commitment $k\in\mathbb R$ and target $L\in\mathbb R$. Let $\varphi$ be a trading strategy with futures gain $G(\varphi)$. Then $\varphi$ solves problem (3), $\min_{\theta\in\Theta}E[(kS_T+G(\theta)_T-L)^2]$, if and only if for every trading strategy $\theta$
--
--   $$\big(L-kS_T-G(\varphi)_T\,\big|\,G(\theta)_T\big)=E\big[(L-kS_T-G(\varphi)_T)\,G(\theta)_T\big]=0,$$
--
--   where the product is integrable.
--
--   This is the projection-theorem characterization of the optimal hedge: the residual $L-kS_T-G(\varphi)_T$ must be orthogonal in $L^2(P)$ to the space of attainable terminal gains.
--
--   **Formalization Note.** $G(\varphi)$ is any fixed version of the gain of $\varphi$; on the right, $G(\theta)$ ranges over all versions. The paper's "$(X|Y)$ on $L^2(P)$" is rendered as integrability of the product together with a vanishing Bochner integral, so a non-integrable product cannot satisfy the condition through Lean's junk value $0$.
-- source:
--   Duffie and Richardson, Mean-Variance Hedging in Continuous Time, Ann. Appl. Probab. 1(1) (1991), Lemma 1 and (8), p. 4

import Mathlib
import Definitions.Def_DuffieHedge_Optimal_Basic

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace DuffieHedge.Optimal

/-- Lemma 1 (p. 4): a trading strategy `φ` solves problem (3) iff, for every trading strategy
`θ`, `(L − kS_T − G(φ)_T | G(θ)_T) = 0`, the inner product of `L²(P)` (the product is integrable
and its expectation vanishes). -/
theorem lemma_1 {Ω : Type*} [MeasurableSpace Ω] (M : Market Ω) (hM : M.Standing) (k L : ℝ)
    (φ Gφ : ℝ≥0 → Ω → ℝ) (hφ : M.IsTradingStrategy φ) (hGφ : M.IsGain φ Gφ) :
    M.SolvesP3 k L φ ↔
      ∀ θ, M.IsTradingStrategy θ → ∀ Gθ, M.IsGain θ Gθ →
        Integrable (fun ω => (L - k * M.S M.T ω - Gφ M.T ω) * Gθ M.T ω) M.P ∧
        ∫ ω, (L - k * M.S M.T ω - Gφ M.T ω) * Gθ M.T ω ∂M.P = 0 := by sorry

end DuffieHedge.Optimal
