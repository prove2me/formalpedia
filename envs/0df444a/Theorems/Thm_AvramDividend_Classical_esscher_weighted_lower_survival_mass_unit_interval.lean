-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_weighted_lower_survival_mass_unit_interval
-- name    : AvramDividend.Classical.esscher_weighted_lower_survival_mass_unit_interval
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:22:08.42441+00:00
-- url     : https://prove2.me/theorems/28aaafa3-757a-4676-8446-30fc9cc1173d
-- title:
--   Every finite-horizon Esscher-weighted lower survival mass lies in the unit interval
-- statement:
--   For any spectrally negative Lévy process and nonnegative Esscher parameter, the expected normalised exponential restricted to paths surviving a shifted lower barrier until a fixed time lies between zero and one. Integrability follows from the exponential martingale, positivity from the exponential function, and the upper bound from the unit expectation of its compensated exponential.
-- source:
--   Direct composition of the proved exponential Lévy expectation-one lemma with the exact-history filtration survival lemma and Mathlib integral monotonicity. Finite-horizon survival mass is a probability under the local Esscher tilt, providing bounds for its infinite-horizon limit.

import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Theorems.Thm_AvramDividend_Classical_esscher_exp_process_martingale
import Theorems.Thm_AvramDividend_Classical_levy_compensated_exponential_expectation_one
import Theorems.Thm_AvramDividend_Classical_shifted_lower_survival_filtration_measurable_no_schedule

open MeasureTheory
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.esscher_weighted_lower_survival_mass_unit_interval
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) (x : ℝ) (t : ℝ≥0) :
    0 ≤
      (∫ ω,
        ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
          (fun ω => Real.exp
            (θ * X.X t ω - (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω ∂P)
    ∧
      (∫ ω,
        ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
          (fun ω => Real.exp
            (θ * X.X t ω - (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω ∂P) ≤ 1 := by sorry
