-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_interior_stopped_moving_mesh_bound
-- name    : AvramDividend.Classical.avram_p4_a_gaussian_original_interior_stopped_moving_mesh_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:42:16.55821+00:00
-- url     : https://prove2.me/theorems/06bb3ecb-6122-4d9c-9717-f686b16af7d7
-- title:
--   Original controlled stopped interior path: uniform moving-mesh Gaussian Taylor bound
-- statement:
--   For the actual original Lévy process X and dividend control D, on the strict open portion 0<=s,t<tau(omega) of any exact interior-localisation clock whose controlled reserve path remains in a source compact band, one uniform K controls the Taylor remainder along every pair of path time points. The only additional hypothesis hLocal is the explicit path-in-band invariant to be provided by P4-E; no global boundary regularity, occupation-time statement, independent Brownian representation or stochastic-integral assertion is made.
-- source:
--   Accepted moving mesh theorem 672c0cae-c6b6-4738-894a-8e8fe4ef0398, original source riskProcess; Avram et al Proposition 4(i).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_ubv_C2_uniform_moving_taylor_quadratic_bound
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_a_gaussian_original_interior_stopped_moving_mesh_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hwC2 : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hBand : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (τ : Ω → ℝ≥0)
    (hLocal : ∀ ω (s : ℝ≥0), s < τ ω → riskProcess X x D s ω ∈ Icc a b) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ ω (s t : ℝ≥0), s < τ ω → t < τ ω →
        riskProcess X x D s ω ≠ riskProcess X x D t ω →
        |w (riskProcess X x D t ω) -
          taylorWithinEval w 1
            (uIcc (riskProcess X x D s ω) (riskProcess X x D t ω))
            (riskProcess X x D s ω) (riskProcess X x D t ω)| ≤
          (K / 2) *
            (riskProcess X x D t ω - riskProcess X x D s ω) ^ 2 := by sorry
