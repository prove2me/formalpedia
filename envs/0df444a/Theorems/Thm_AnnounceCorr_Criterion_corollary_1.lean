-- Prove2me | Theorems.Thm_AnnounceCorr_Criterion_corollary_1
-- name    : AnnounceCorr.Criterion.corollary_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:16:02.572177+00:00
-- url     : https://prove2.me/theorems/5e43ca18-9a4d-43b4-80a3-5778dce04ac2
-- title:
--   Corollary 1, p. 14 — EA has no larger MSE iff correlation is at most 1/2
-- statement:
--   Let $W_D$ be a square-integrable real waiting time with positive variance, and let $P$ be a square-integrable real predictor on the same probability space. Suppose $P$ has the same mean and variance as $W_D$. With EA the constant predictor $\mathbb E[W_D]$ and $r[P,W_D]$ their Pearson correlation, the paper's criterion is
--
--   $$
--   \operatorname{MSE}(\operatorname{EA})\le\operatorname{MSE}(P)
--     \quad\Longleftrightarrow\quad r[P,W_D]\le\frac12.
--   $$
--
--   Thus the correlation threshold determines whether the static announcement is at least as accurate, in mean-squared error, as a predictor with the delay's mean and variance.
--
--   **Formalization Note** Lean states square integrability and positive variance explicitly so MSE, variance, and correlation have their intended values. The result is about the pair's joint law and applies irrespective of the particular queueing model.
-- source:
--   Bassamboo & Ibrahim, A General Framework to Compare Announcement Accuracy, submitted manuscript (Management Science, manuscript XXX; published as doi:10.1287/mnsc.2020.3722), p. 14 (PDF 14), Corollary 1, eq. (5)

import Mathlib
import Definitions.Def_AnnounceCorr_Criterion_Defs

namespace AnnounceCorr.Criterion

open MeasureTheory ProbabilityTheory

/-- Corollary 1, p. 14, equation (5). -/
theorem corollary_1 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (WD P : Ω → ℝ) (hWD : MemLp WD 2 μ)
    (hP : MemLp P 2 μ) (hVarPos : 0 < Var[WD; μ])
    (hMean : ∫ ω, P ω ∂μ = ∫ ω, WD ω ∂μ)
    (hVar : Var[P; μ] = Var[WD; μ]) :
    mse μ WD (ea μ WD) ≤ mse μ WD P ↔ corr μ P WD ≤ 1 / 2 := by sorry

end AnnounceCorr.Criterion
