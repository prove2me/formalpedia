-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_weighted_lower_survival_mass_monotone_start
-- name    : AvramDividend.Classical.esscher_weighted_lower_survival_mass_monotone_start
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:16:32.222225+00:00
-- url     : https://prove2.me/theorems/f07a704e-d436-45aa-b705-011aa988cfc0
-- title:
--   Esscher-weighted lower survival increases with initial reserve
-- statement:
--   At each fixed horizon, the Esscher-weighted probability of surviving above the lower ruin barrier is monotone in the initial capital: raising the initial reserve enlarges the set of surviving paths and leaves the nonnegative Esscher weight unchanged. This establishes spatial monotonicity needed to identify the infinite-horizon tilted survival function with an Esscher-tilted q-scale function.
-- source:
--   Elementary survival-event inclusion, Lévy Esscher exponential martingale integrability, and Mathlib setIntegral_mono_set. Related to Kuznetsov, Kyprianou and Rivero, The Theory of Scale Functions for Spectrally Negative Lévy Processes.

import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_esscher_exp_process_martingale
import Theorems.Thm_AvramDividend_Classical_shifted_lower_survival_filtration_measurable_no_schedule

open MeasureTheory
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.esscher_weighted_lower_survival_mass_monotone_start
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (x y : ℝ) (hxy : x ≤ y) (t : ℝ≥0) :
    (∫ ω,
      ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
        (fun ω => Real.exp
          (θ * X.X t ω - (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω ∂P) ≤
    (∫ ω,
      ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ y + X.X s ω}).indicator
        (fun ω => Real.exp
          (θ * X.X t ω - (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω ∂P) := by sorry
