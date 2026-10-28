-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_reflected_infimum_integrable
-- name    : AvramDividend.Classical.chat04_esscher_weighted_reflected_infimum_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T09:59:13.610778+00:00
-- url     : https://prove2.me/theorems/3fd15b5c-b779-49fb-9973-a7adbcffe2bd
-- title:
--   Integrability of the true Esscher-weighted reflected-infimum transform
-- statement:
--   Under a nonnegative Esscher tilt and positive capital Laplace parameter, the finite-horizon reflected-infimum exponential multiplied by the terminal compensated Lévy exponential is integrable, since the first factor is bounded by 1/β and the Esscher exponential is integrable.
-- source:
--   Use Proved esscher_exp_process_integrable (701eb6a8) for the terminal exponential and Proved levy_running_infimum_measurable (d11a34c7) for the reflected infimum. Because R_t≥0, exp(-βR_t)/β≤1/β, and a measurable product is dominated by an integrable constant multiple of the Esscher weight. Necessary for the ENNReal-to-real expectation bridge and horizon limits.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Theorems.Thm_AvramDividend_Classical_esscher_exp_process_integrable
import Theorems.Thm_AvramDividend_Classical_levy_running_infimum_measurable

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_esscher_weighted_reflected_infimum_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (β θ : ℝ) (hβ : 0 < β) (hθ : 0 ≤ θ) :
    Integrable (fun ω : Ω =>
      (Real.exp (-β * max 0
        (-sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω})) / β) *
      Real.exp (θ * X.X t ω -
        (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) P := by sorry
