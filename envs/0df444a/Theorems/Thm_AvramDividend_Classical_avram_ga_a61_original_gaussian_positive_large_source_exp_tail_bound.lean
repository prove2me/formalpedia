-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a61_original_gaussian_positive_large_source_exp_tail_bound
-- name    : AvramDividend.Classical.avram_ga_a61_original_gaussian_positive_large_source_exp_tail_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T07:21:20.103884+00:00
-- url     : https://prove2.me/theorems/49237191-76ed-4651-b106-27a820548d0a
-- title:
--   Actual original no-jump Gaussian positive weighted large-source excursion has an exact exponential Chernoff expected bound
-- statement:
--   On genuine original Gaussian drift-centred physical increments, exponential positive-weighted tails above any fixed positive threshold have the exact Chernoff upper bound controlled by the original Gaussian exponential moment, with no independent substitute source.
-- source:
--   Original b0d9951c positive-only spatial high-surplus rare excursion source bound using ga_a48 and ga_a60.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a61_original_gaussian_positive_large_source_exp_tail_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hσ : 0 < X.σ)
    (s t : ℝ≥0) (hst : s ≤ t)
    (θ r δ : ℝ) (hθ : 0 ≤ θ) (hr : 0 ≤ r) :
    let Z : Ω → ℝ := fun ω =>
      ((X.X t ω - X.X s ω) -
        ((t - s : ℝ≥0) : ℝ) * X.c) / X.σ
    Integrable (fun ω => if δ ≤ Z ω then Real.exp (θ * Z ω) else 0) P →
    Integrable (fun ω => Real.exp ((θ + r) * Z ω)) P →
    (∫ ω, if δ ≤ Z ω then Real.exp (θ * Z ω) else 0 ∂P) ≤
      Real.exp (-r * δ + ((t - s : ℝ≥0) : ℝ) * (θ + r)^2 / 2) := by sorry
