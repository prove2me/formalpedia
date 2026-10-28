-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_esscher_perpetual_infimum_finite_distribution_measure
-- name    : AvramDividend.Classical.chat04_esscher_perpetual_infimum_finite_distribution_measure
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T17:39:18.434908+00:00
-- url     : https://prove2.me/theorems/b5b4b8e7-ccfb-4c6e-8835-55f511eebec8
-- title:
--   Finite Borel measure with exact perpetual Esscher survival CDF
-- statement:
--   The infinite-horizon Esscher survival function of a spectrally negative Lévy process equals the closed-lower-half-line cumulative law of a genuinely finite Borel measure on the real line. The measure is allowed to be defective, and its exact cumulative mass is the infimum of the weighted finite-horizon killed-survival probabilities.
-- source:
--   The accepted Stieltjes construction gives a real CDF. The accepted zero-left-tail and Stieltjes half-line formula give exact evaluation of its associated measure, while unit-interval boundedness and the accepted finite-Stieltjes theorem provide finite total measure. None of these steps assumes the Wiener-Hopf numerical transform or the canonical q-scale exit identity.

import Mathlib.MeasureTheory.Measure.Stieltjes
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_infinite_survival_stieltjes_measure
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_infimum_survival_zero_negative_reserve
import Theorems.Thm_AvramDividend_Classical_stieltjes_measure_Iic_of_zero_negative
import Theorems.Thm_AvramDividend_Classical_stieltjes_isFiniteMeasure_of_zero_negative_bounded_one
import Theorems.Thm_AvramDividend_Classical_esscher_weighted_lower_survival_mass_unit_interval
open MeasureTheory Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_esscher_perpetual_infimum_finite_distribution_measure
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ : ℝ) (hθ : 0 ≤ θ) :
    ∃ ν : Measure ℝ, IsFiniteMeasure ν ∧
      ∀ x : ℝ, ν (Iic x) = (⨅ t : ℝ≥0, ENNReal.ofReal (∫ ω, ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator (fun ω => Real.exp (θ * X.X t ω - (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω ∂P)) := by sorry
