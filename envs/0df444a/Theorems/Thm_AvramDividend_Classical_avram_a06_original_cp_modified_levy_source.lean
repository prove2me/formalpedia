-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_original_cp_modified_levy_source
-- name    : AvramDividend.Classical.avram_a06_original_cp_modified_levy_source
-- status  : Open
-- author  : @WillR
-- created : 2026-11-10T22:27:12.216188+00:00
-- url     : https://prove2.me/theorems/3984994d-eede-45b8-be9b-21001a37fa88
-- title:
--   Original compound Poisson admits an all-path zero-start downward-jump Lévy modification
-- statement:
--   Construct a measurable all-path zero-start càdlàg downward-jump modification of the original compound-Poisson process on the original probability space, retaining almost-sure equality at each deterministic time and a full Lévy-process independent/stationary increment structure. The driver imposes regular arrivals only almost surely, so demanding that the raw source itself literally starts at zero is too strong. The separate natural-filtration upgrade is already covered by a Proved theorem.
-- source:
--   Corrected alternative to the raw-isLevyProcess branch of d4e19a1a; source-specific stochastic-increment certificate after a.e. correction.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory Set ProbabilityTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_original_cp_modified_levy_source
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
    [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P) :
    ∃ (Z : ℝ≥0 → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ),
      IsLevyProcess Z P ∧
      (∀ ω, Z 0 ω = 0) ∧
      (∀ ω t, ContinuousWithinAt (fun s => Z s ω) (Ici t) t) ∧
      (∀ ω t, 0 < t →
        ∃ l, Tendsto (fun s => Z s ω) (nhdsWithin t (Iio t)) (nhds l)) ∧
      (∀ ω t l, 0 < t →
        Tendsto (fun s => Z s ω) (nhdsWithin t (Iio t)) (nhds l) →
        Z t ω ≤ l) ∧
      (∀ t, Measurable (Z t)) ∧
      (∀ t : ℝ≥0,
        Z t =ᵐ[P] LevyFoundations.compoundPoisson (1 : ℝ) τ Y (t : ℝ)) := by sorry
