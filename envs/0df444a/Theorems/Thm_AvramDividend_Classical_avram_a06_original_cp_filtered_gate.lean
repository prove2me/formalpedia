-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_original_cp_filtered_gate
-- name    : AvramDividend.Classical.avram_a06_original_cp_filtered_gate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T20:22:09.566961+00:00
-- url     : https://prove2.me/theorems/962fdfab-3164-480a-bfad-e2553b8037d9
-- title:
--   Original compound-Poisson Lévy path has an everywhere càdlàg downward-jump filtered modification
-- statement:
--   Given the original canonical compound-Poisson path as a Lévy process on the same probability space, use the public almost-sure càdlàg, zero-start, simultaneous negative-mark results and measurable gating to construct all-path càdlàg downward-jump modification with a natural adapted filtration and unchanged increment laws.
-- source:
--   Original pathwise/all-path modification prerequisite for certificate d4e19a1a; source-specific raw IsLevyProcess is an explicit input.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory Set ProbabilityTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_original_cp_filtered_gate
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
    [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P)
    (hraw : IsLevyProcess
      (fun t : ℝ≥0 => LevyFoundations.compoundPoisson (1 : ℝ) τ Y (t : ℝ)) P) :
    ∃ (𝓕 : Filtration ℝ≥0
        (inferInstance : MeasurableSpace ((ℕ → ℝ) × (ℕ → ℝ))))
      (Z : ℝ≥0 → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ),
      (∀ ω, Z 0 ω = 0) ∧
      (∀ ω t, ContinuousWithinAt (fun s => Z s ω) (Ici t) t) ∧
      (∀ ω t, 0 < t →
        ∃ l, Tendsto (fun s => Z s ω) (nhdsWithin t (Iio t)) (nhds l)) ∧
      (∀ ω t l, 0 < t →
        Tendsto (fun s => Z s ω) (nhdsWithin t (Iio t)) (nhds l) →
        Z t ω ≤ l) ∧
      Adapted 𝓕 Z ∧
      (∀ s t, s ≤ t →
        Indep (MeasurableSpace.comap
          (fun ω => Z t ω - Z s ω) inferInstance) (𝓕 s) P) ∧
      (∀ s t, s ≤ t →
        IdentDistrib (fun ω => Z t ω - Z s ω)
          (Z (t - s)) P P) ∧
      (∀ t : ℝ≥0,
        Z t =ᵐ[P] LevyFoundations.compoundPoisson (1 : ℝ) τ Y (t : ℝ)) := by sorry
