-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_esscher_infinite_survival_stieltjes_measure
-- name    : AvramDividend.Classical.chat04_esscher_infinite_survival_stieltjes_measure
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T17:21:56.237003+00:00
-- url     : https://prove2.me/theorems/96c31ba1-d0ae-44da-a91a-a7620b9106a7
-- title:
--   Stieltjes representation of perpetual Esscher survival
-- statement:
--   Construct an exact Stieltjes function representing the perpetual Esscher survival cumulative law.
-- source:
--   Combine accepted monotonicity, right continuity and boundedness with the generic Stieltjes function constructor.

import Mathlib.MeasureTheory.Measure.Stieltjes
import Theorems.Thm_AvramDividend_Classical_ennreal_monotone_right_continuous_stieltjes
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_survival_ennreal_infimum_right_continuous
import Theorems.Thm_AvramDividend_Classical_esscher_weighted_lower_survival_mass_monotone_start
import Theorems.Thm_AvramDividend_Classical_esscher_weighted_lower_survival_mass_unit_interval
open MeasureTheory Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_esscher_infinite_survival_stieltjes_measure {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (θ : ℝ) (hθ : 0 ≤ θ) : ∃ S : StieltjesFunction ℝ, ∀ x : ℝ, S x = (⨅ t : ℝ≥0, ENNReal.ofReal (∫ ω, ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator (fun ω => Real.exp (θ * X.X t ω - (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω ∂P)).toReal := by sorry
