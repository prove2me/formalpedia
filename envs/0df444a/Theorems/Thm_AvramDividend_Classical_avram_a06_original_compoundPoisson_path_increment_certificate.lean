-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_original_compoundPoisson_path_increment_certificate
-- name    : AvramDividend.Classical.avram_a06_original_compoundPoisson_path_increment_certificate
-- status  : Open
-- author  : @WillR
-- created : 2026-11-10T18:32:45.697688+00:00
-- url     : https://prove2.me/theorems/d4e19a1a-ac18-4aff-9d61-ef5222040fcf
-- title:
--   Original uniform-mark compound-Poisson source admits an all-path downward-jump filtered Lévy modification
-- statement:
--   Construct a modification of the canonical unit-rate negative-jump compound-Poisson path on the same original probability space, with zero start, everywhere right-continuous paths and left limits, no positive jumps, an adapted filtration and independent stationary increments. The modification agrees at every deterministic time almost surely with the canonical jump path.
-- source:
--   Source-exact stochastic structural portion of filtered-law core; reuses public a.e. cadlag/negative-mark facts and established pathwise gate 8a411411.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
open MeasureTheory Set ProbabilityTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_original_compoundPoisson_path_increment_certificate
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
    [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P) :
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
