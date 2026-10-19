-- Prove2me | Theorems.Thm_AnnounceCorr_Criterion_proposition_1_expansion
-- name    : AnnounceCorr.Criterion.proposition_1_expansion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:15:47.161458+00:00
-- url     : https://prove2.me/theorems/0f08e358-8263-443e-83df-cd7bb3532b41
-- title:
--   Proof of Proposition 1, p. 14 — expanded mean-squared error
-- statement:
--   Let $W_D$ be the waiting time of a delayed customer and $P$ its predictor, both square-integrable on the same probability space. Suppose $\operatorname{Var}(W_D)>0$, $\gamma,\beta\ge0$, $\mathbb E[P]=\gamma\mathbb E[W_D]$, and $\operatorname{Var}(P)=\beta\operatorname{Var}(W_D)$. Write $r[P,W_D]$ for their Pearson correlation. The expansion displayed in the proof of Proposition 1 is
--
--   $$
--   \operatorname{MSE}(P)=\operatorname{Var}(P)+\operatorname{Var}(W_D)
--     +(\gamma-1)^2(\mathbb E[W_D])^2
--     -2r[P,W_D]\sqrt\beta\,\operatorname{Var}(W_D).
--   $$
--
--   This is the unnormalized error identity used immediately before equation (4).
--
--   **Formalization Note** The paper assumes finite moments implicitly; Lean states $L^2$ membership. Positive variance of $W_D$ makes the Pearson term meaningful when $\beta>0$. At $\beta=0$ Lean's zero-division convention sets correlation to zero, and its multiplier $\sqrt\beta$ vanishes.
-- source:
--   Bassamboo & Ibrahim, A General Framework to Compare Announcement Accuracy, submitted manuscript (Management Science, manuscript XXX; published as doi:10.1287/mnsc.2020.3722), p. 14 (PDF 14), proof of Proposition 1, second display line

import Mathlib
import Definitions.Def_AnnounceCorr_Criterion_Defs

namespace AnnounceCorr.Criterion

open MeasureTheory ProbabilityTheory

/-- The second display line in the proof of Proposition 1, p. 14. -/
theorem proposition_1_expansion {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (WD P : Ω → ℝ) (hWD : MemLp WD 2 μ)
    (hP : MemLp P 2 μ) (hVarPos : 0 < Var[WD; μ])
    (γ β : ℝ) (hγ : 0 ≤ γ) (hβ : 0 ≤ β)
    (hMean : ∫ ω, P ω ∂μ = γ * ∫ ω, WD ω ∂μ)
    (hVar : Var[P; μ] = β * Var[WD; μ]) :
    mse μ WD P = Var[P; μ] + Var[WD; μ] +
      (γ - 1) ^ 2 * (∫ ω, WD ω ∂μ) ^ 2 -
      2 * corr μ P WD * Real.sqrt β * Var[WD; μ] := by sorry

end AnnounceCorr.Criterion
