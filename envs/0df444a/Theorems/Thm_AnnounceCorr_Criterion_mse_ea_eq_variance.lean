-- Prove2me | Theorems.Thm_AnnounceCorr_Criterion_mse_ea_eq_variance
-- name    : AnnounceCorr.Criterion.mse_ea_eq_variance
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:15:50.359102+00:00
-- url     : https://prove2.me/theorems/b61c053e-ec25-4cc3-8ac2-e2323b0d9deb
-- title:
--   §4.2, p. 14 — MSE(EA) equals Var[W_D]
-- statement:
--   Let $W_D$ be a square-integrable real waiting time on a probability space. The static announcement EA always predicts its mean, $\mathbb E[W_D]$. Its mean-squared prediction error is
--
--   $$
--   \operatorname{MSE}(\operatorname{EA})
--     =\mathbb E[(W_D-\mathbb E[W_D])^2]
--     =\operatorname{Var}(W_D).
--   $$
--
--   This identifies the benchmark against which the paper compares a dynamic announcement.
--
--   **Formalization Note** Square integrability is explicit so both the real integral and variance retain their usual mathematical meanings.
-- source:
--   Bassamboo & Ibrahim, A General Framework to Compare Announcement Accuracy, submitted manuscript (Management Science, manuscript XXX; published as doi:10.1287/mnsc.2020.3722), p. 14 (PDF 14), §4.2, paragraph following eq. (3)

import Mathlib
import Definitions.Def_AnnounceCorr_Criterion_Defs

namespace AnnounceCorr.Criterion

open MeasureTheory ProbabilityTheory

/-- Section 4.2, p. 14: the EA prediction has MSE equal to the delay variance. -/
theorem mse_ea_eq_variance {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (WD : Ω → ℝ) (hWD : MemLp WD 2 μ) :
    mse μ WD (ea μ WD) = Var[WD; μ] := by sorry

end AnnounceCorr.Criterion
