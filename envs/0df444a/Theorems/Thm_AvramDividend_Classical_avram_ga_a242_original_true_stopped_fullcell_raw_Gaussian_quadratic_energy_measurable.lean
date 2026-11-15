-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a242_original_true_stopped_fullcell_raw_Gaussian_quadratic_energy_measurable
-- name    : AvramDividend.Classical.avram_ga_a242_original_true_stopped_fullcell_raw_Gaussian_quadratic_energy_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:15:42.382316+00:00
-- url     : https://prove2.me/theorems/758c9c25-74af-430d-b584-187d86da41d1
-- title:
--   Original stopped Gaussian true full physical-grid raw second-energy finite sum measurable
-- statement:
--   Every true original finite-horizon Gaussian physical grid sum of nonnegative squared raw Lévy increments over wholly pre-stopping-time cells is measurable. Actual stopped full cells use the conjunction of start before rho and end at or before rho, and each raw Gaussian increment is measurable by the original Lévy process adaptedness. This exact source supplies AEStronglyMeasurable for the Gaussian raw quadratic integrability lemma a241.
-- source:
--   Original X.adapted and rho IsStoppingTime.rightCont.mappable; Finset measurable sum for full-cell raw square

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a242_original_true_stopped_fullcell_raw_Gaussian_quadratic_energy_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (n : ℕ) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0))) :
    ∀ m : ℕ, Measurable (fun ω : Ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      ∑ i ∈ Finset.range m,
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        let R : ℝ := X.X (s + Δ) ω - X.X s ω
        if s < ρ ω ∧ s + Δ ≤ ρ ω
        then R^2 else 0) := by sorry
