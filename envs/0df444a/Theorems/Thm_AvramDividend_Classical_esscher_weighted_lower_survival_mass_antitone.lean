-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_weighted_lower_survival_mass_antitone
-- name    : AvramDividend.Classical.esscher_weighted_lower_survival_mass_antitone
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:05:44.127334+00:00
-- url     : https://prove2.me/theorems/6335f5be-f179-4a41-94d1-3ff13c44d829
-- title:
--   Esscher-weighted lower-barrier survival mass decreases with time
-- statement:
--   For a spectrally negative Lévy process and every nonnegative Esscher parameter, the expected exponential-martingale mass on paths staying above a shifted lower barrier throughout a time horizon decreases as the horizon increases. This directly combines the Esscher exponential martingale with filtration-measurable closed-horizon survival and nonnegative martingale monotonicity.
-- source:
--   Derived from the Esscher change-of-measure proof of scale-function harmonicity in Kuznetsov, Kyprianou and Rivero, The Theory of Scale Functions for Spectrally Negative Lévy Processes, Section 2.2. Remote Lean compilation of the exact proof source passed before the intentional sentinel.

import Theorems.Thm_AvramDividend_Classical_esscher_exp_process_martingale
import Theorems.Thm_AvramDividend_Classical_nonnegative_martingale_survival_mass_antitone
import Theorems.Thm_AvramDividend_Classical_shifted_lower_survival_filtration_measurable_no_schedule

open MeasureTheory
open scoped NNReal

theorem AvramDividend.Classical.esscher_weighted_lower_survival_mass_antitone
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) (x : ℝ)
    (t u : ℝ≥0) (htu : t ≤ u) :
    (∫ ω,
      ({ω | ∀ s : ℝ≥0, s ≤ u → 0 ≤ x + X.X s ω}).indicator
        (fun ω => Real.exp
          (θ * X.X u ω - (u : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω ∂P) ≤
    (∫ ω,
      ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
        (fun ω => Real.exp
          (θ * X.X t ω - (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω ∂P) := by sorry
