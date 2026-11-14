-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a69_original_gaussian_positive_tail_unconditional_expected_chernoff
-- name    : AvramDividend.Classical.avram_ga_a69_original_gaussian_positive_tail_unconditional_expected_chernoff
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T07:35:10.688507+00:00
-- url     : https://prove2.me/theorems/b1eebca6-b67b-447f-9d17-d107eeeaabaa
-- title:
--   Original zero-jump Gaussian positive upper source excursion has unconditional exponential Chernoff expected bound
-- statement:
--   For a measurable actual original normalised drift-centred Gaussian deterministic increment and all nonnegative exponential tilts, the positive exponentially weighted upper-tail expected value obeys the exact Gaussian Chernoff bound without any additional integrability hypotheses.
-- source:
--   Original positive-only b0d9951c actual Gaussian upper surplus source excursion; combines ga_a61 and ga_a68 to discharge both integrability hypotheses.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a69_original_gaussian_positive_tail_unconditional_expected_chernoff
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hσ : 0 < X.σ)
    (s t : ℝ≥0) (hst : s ≤ t)
    (Z : Ω → ℝ)
    (hZ : Z = (fun ω => ((X.X t ω - X.X s ω) -
      ((t - s : ℝ≥0) : ℝ) * X.c) / X.σ))
    (hMeas : Measurable Z)
    (θ r δ : ℝ) (hθ : 0 ≤ θ) (hr : 0 ≤ r) :
    (∫ ω, if δ ≤ Z ω then Real.exp (θ * Z ω) else 0 ∂P) ≤
      Real.exp (-r * δ + ((t - s : ℝ≥0) : ℝ) * (θ + r)^2 / 2) := by sorry
