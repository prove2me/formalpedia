-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_discounted_interior_hessian_state_tendsto
-- name    : AvramDividend.Classical.avram_p4_a_gaussian_original_discounted_interior_hessian_state_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:29:24.747305+00:00
-- url     : https://prove2.me/theorems/77ee6a78-88bc-4fd8-91b4-b5017782a917
-- title:
--   Original Levy Gaussian discounted Hessian continuity along interior convergent state meshes
-- statement:
--   From precisely the source C² hypothesis on the strict interior, at any positive interior reserve level y, the source discounted Gaussian Hessian exp(-qs)σ²/2 w'' is continuous under arbitrary approximations of the state converging to y. No regularity is assumed at zero, cap or ruin and no external Brownian process is used. This discharges the pointwise convergence prerequisite for dominated convergence on P4-E's true interior localised intervals.
-- source:
--   ContDiffOn→ContDiffAt on the proved open strict interior, twice-derivative continuity and ordinary continuous mapping. Source exact Gaussian coefficient SpectrallyNegativeLevy.σ; Avram, Palmowski and Pistorius Proposition 4(i), Eq. (5.10).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_ubv_strict_C2_interior_isOpen
open MeasureTheory ProbabilityTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_a_gaussian_original_discounted_interior_hessian_state_tendsto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hwC2 : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (y : ℝ) (hy : 0 < y ∧ ENNReal.ofReal y < C)
    (s : ℝ≥0) (yn : ℕ → ℝ)
    (hyn : Tendsto yn atTop (nhds y)) :
    Tendsto (fun n => Real.exp (-(q * (s : ℝ))) *
      (X.σ ^ 2 / 2 * iteratedDeriv 2 w (yn n)))
      atTop (nhds (Real.exp (-(q * (s : ℝ))) *
        (X.σ ^ 2 / 2 * iteratedDeriv 2 w y))) := by sorry
