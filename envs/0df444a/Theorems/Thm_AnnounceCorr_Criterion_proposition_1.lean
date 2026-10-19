-- Prove2me | Theorems.Thm_AnnounceCorr_Criterion_proposition_1
-- name    : AnnounceCorr.Criterion.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:15:48.911532+00:00
-- url     : https://prove2.me/theorems/9040bf92-6886-4514-8b4a-10ddf2243751
-- title:
--   Proposition 1, p. 14 — normalized MSE identity
-- statement:
--   Let $W_D$ be the waiting time of a delayed customer and $P$ its predictor, both square-integrable on the same probability space. Suppose $\operatorname{Var}(W_D)>0$, $\mathbb E[W_D]>0$, $\gamma,\beta\ge0$, $\mathbb E[P]=\gamma\mathbb E[W_D]$, and $\operatorname{Var}(P)=\beta\operatorname{Var}(W_D)$. Let $r[P,W_D]$ be their Pearson correlation and $C_{W_D}=\sqrt{\operatorname{Var}(W_D)}/\mathbb E[W_D]$. Then
--
--   $$
--   \operatorname{MSE}(P)=\operatorname{Var}(W_D)
--     \left(\beta+1+\left(\frac{\gamma-1}{C_{W_D}}\right)^2
--     -2r[P,W_D]\sqrt\beta\right).
--   $$
--
--   The identity expresses prediction error in terms of bias, relative variance, and correlation, allowing static and dynamic announcements to be compared on a common scale.
--
--   **Formalization Note** The paper's finite-moment convention is explicit as $L^2$ membership. Positive mean and variance of $W_D$ ensure that the coefficient of variation and normalized formula have their intended meaning. The case $\beta=0$ remains included.
-- source:
--   Bassamboo & Ibrahim, A General Framework to Compare Announcement Accuracy, submitted manuscript (Management Science, manuscript XXX; published as doi:10.1287/mnsc.2020.3722), p. 14 (PDF 14), Proposition 1, eq. (4)

import Mathlib
import Definitions.Def_AnnounceCorr_Criterion_Defs

namespace AnnounceCorr.Criterion

open MeasureTheory ProbabilityTheory

/-- Proposition 1, p. 14, equation (4). -/
theorem proposition_1 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (WD P : Ω → ℝ) (hWD : MemLp WD 2 μ)
    (hP : MemLp P 2 μ) (hVarPos : 0 < Var[WD; μ])
    (hMeanPos : 0 < ∫ ω, WD ω ∂μ)
    (γ β : ℝ) (hγ : 0 ≤ γ) (hβ : 0 ≤ β)
    (hMean : ∫ ω, P ω ∂μ = γ * ∫ ω, WD ω ∂μ)
    (hVar : Var[P; μ] = β * Var[WD; μ]) :
    mse μ WD P = Var[WD; μ] *
      (β + 1 + ((γ - 1) / coeffVar μ WD) ^ 2 -
        2 * corr μ P WD * Real.sqrt β) := by sorry

end AnnounceCorr.Criterion
