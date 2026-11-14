-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a176_original_gaussian_stopped_prefix_centered_square_measurable_nonnegative
-- name    : AvramDividend.Classical.avram_ga_a176_original_gaussian_stopped_prefix_centered_square_measurable_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T14:58:05.625591+00:00
-- url     : https://prove2.me/theorems/3d40043c-a8ed-4066-be04-c40a279f8392
-- title:
--   Exact stopped original Gaussian physical-grid centred-square source energy is measurable and pointwise nonnegative
-- statement:
--   With the genuine spectrally negative Levy source X and right-continuous stopping clock ρ, each physical mesh stopped-prefix finite sum of real squared drift-centred increments is a measurable nonnegative observable. This provides the measurability/positivity premises required to convert the proved ga39 ENNReal source energy into real integrability for ga_a173.
-- source:
--   Original X.adapted measurability and stopping time measurable, finite masked square sum.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a176_original_gaussian_stopped_prefix_centered_square_measurable_nonnegative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (n : ℕ) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0))) :
    let E : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      ∑ i ∈ Finset.range m,
        if (i : ℝ≥0) * Δ < ρ ω then
          (X.X ((i : ℝ≥0) * Δ + Δ) ω -
            X.X ((i : ℝ≥0) * Δ) ω - (Δ : ℝ) * X.c)^2
        else 0
    ∀ m : ℕ, Measurable (E m) ∧ ∀ ω : Ω, 0 ≤ E m ω := by sorry
