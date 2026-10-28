-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_reflected_transform_unit_bound
-- name    : AvramDividend.Classical.chat04_esscher_weighted_reflected_transform_unit_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T11:07:53.621711+00:00
-- url     : https://prove2.me/theorems/d204e00c-ea24-4b5e-80a7-dfe8f2d1b075
-- title:
--   Uniform unit-mass bound for Esscher-weighted reflected-infimum Laplace expectations
-- statement:
--   At every finite time, the Esscher-weighted reflected running-infimum real expectation is nonnegative and bounded above by the inverse capital Laplace parameter. The bound is uniform over horizons and relies on the exact unit expectation of the normalised Lévy exponential.
-- source:
--   Already Proved weighted reflected-infimum integrability, Esscher exponential integrability and compensated exponential expectation one. Use 0≤exp(-βR_t)/β≤1/β and Bochner integral monotonicity. Supplies uniform L1 and transform bounds required to extract the infinite-horizon survival potential independently of the two-sided exit identity.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_reflected_infimum_integrable
import Theorems.Thm_AvramDividend_Classical_esscher_exp_process_integrable
import Theorems.Thm_AvramDividend_Classical_levy_compensated_exponential_expectation_one

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_esscher_weighted_reflected_transform_unit_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (β θ : ℝ) (hβ : 0 < β) (hθ : 0 ≤ θ) :
    0 ≤ (∫ ω : Ω,
      (Real.exp (-β * max 0
        (-sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω})) / β) *
      Real.exp (θ * X.X t ω -
        (t : ℝ) * laplaceExponent X.c X.σ X.ν θ) ∂P) ∧
    (∫ ω : Ω,
      (Real.exp (-β * max 0
        (-sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω})) / β) *
      Real.exp (θ * X.X t ω -
        (t : ℝ) * laplaceExponent X.c X.σ X.ν θ) ∂P) ≤ 1 / β := by sorry
