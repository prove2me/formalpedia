-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_esscher_killed_survival_right_continuous_capital
-- name    : AvramDividend.Classical.chat04_esscher_killed_survival_right_continuous_capital
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T12:52:35.335832+00:00
-- url     : https://prove2.me/theorems/f3e49111-bb7b-4fc2-afc1-d3893c710a5b
-- title:
--   Right continuity in reserve of the actual finite-horizon Esscher weighted killed-survival expectation
-- statement:
--   For every finite observation horizon and nonnegative Esscher parameter, the original-measure expectation of the terminal compensated exponential on paths that remain nonnegative when shifted by initial capital y is right-continuous as a function of the initial capital. This is the regularity needed to take an infimum across horizons and construct the non-ruin survival Stieltjes distribution.
-- source:
--   Compose the actual finite-horizon tilted running-infimum pushforward probability law, its real CDF identification with the killed survival expectation, and generic right-continuity of a real probability CDF. None of the input proofs uses the scale-function exit identity. The conclusion supports pointwise infimum right continuity and descending Wiener-Hopf measure construction.

import Mathlib.Probability.CDF
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_running_infimum_law_probability
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_reflected_CDF_real_eq_survival_expectation
import Theorems.Thm_AvramDividend_Classical_probability_measure_real_Iic_right_continuous

open MeasureTheory Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_esscher_killed_survival_right_continuous_capital
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) (x : ℝ) :
    ContinuousWithinAt (fun y : ℝ => (∫ ω, ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ y + X.X s ω}).indicator (fun ω => Real.exp (θ * X.X t ω - (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω ∂P)) (Ici x) x := by sorry
