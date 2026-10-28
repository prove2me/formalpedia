-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_esscher_reflected_CDF_real_eq_survival_expectation
-- name    : AvramDividend.Classical.chat04_esscher_reflected_CDF_real_eq_survival_expectation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T12:49:26.858476+00:00
-- url     : https://prove2.me/theorems/44b56205-0085-48df-a797-61c68e524cd6
-- title:
--   The actual finite Esscher running-infimum real CDF equals weighted killed-survival expectation
-- statement:
--   For every finite horizon, nonnegative Esscher parameter and initial capital, the real probability of the negative running infimum lying below that capital under the finite Esscher law equals the ordinary real expectation of the terminal compensated exponential on paths avoiding ruin through the entire horizon. This identifies the true real-valued Esscher survival CDF, not merely its Laplace integral.
-- source:
--   Combine accepted 16319 (`chat04_esscher_reflected_law_Iic_eq_killed_lintegral`) with accepted 16121 (nonnegative-to-real integral conversion). The already Proved unit-interval bound ensures the survival expectation is nonnegative, allowing `ENNReal.toReal_ofReal`. Use pinned `Measure.real_def` to convert the pushforward's ENNReal mass. This is the exact finite-time bridge needed before applying Stieltjes CDF regularity and right-continuity of the infinite-horizon infimum.

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_reflected_law_Iic_eq_killed_lintegral
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_killed_survival_real_to_lintegral
import Theorems.Thm_AvramDividend_Classical_esscher_weighted_lower_survival_mass_unit_interval

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_esscher_reflected_CDF_real_eq_survival_expectation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (θ x : ℝ) (hθ : 0 ≤ θ) :
    ((P.withDensity (fun ω : Ω => ENNReal.ofReal (Real.exp (θ * X.X t ω - (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)))).map (fun ω : Ω => -sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω})).real (Iic x) =
    (∫ ω, ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator (fun ω => Real.exp (θ * X.X t ω - (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω ∂P) := by sorry
