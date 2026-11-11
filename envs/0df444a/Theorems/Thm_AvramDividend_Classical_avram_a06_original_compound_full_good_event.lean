-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_original_compound_full_good_event
-- name    : AvramDividend.Classical.avram_a06_original_compound_full_good_event
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T22:48:53.950327+00:00
-- url     : https://prove2.me/theorems/9a1ae714-2874-4b49-b82f-4d3efb3d9de6
-- title:
--   Original marked Poisson source has one measurable full-measure event of zero-start and downward cadlag paths
-- statement:
--   Extract one measurable full-probability sample set on which the original unit-drift compound-Poisson path starts at zero, is right-continuous and has left limits at all positive times, with no positive left jumps. This follows from positive diverging arrivals and all negative marks, including an event measurability regularisation.
-- source:
--   A06 corrected source decomposition, pathwise regularity child of 3984994d.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory Set ProbabilityTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_original_compound_full_good_event
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
    [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P) :
    ∃ G : Set ((ℕ → ℝ) × (ℕ → ℝ)),
      MeasurableSet G ∧
      (∀ᵐ ω ∂P, ω ∈ G) ∧
      (∀ ω ∈ G, LevyFoundations.compoundPoisson (1 : ℝ) τ Y 0 ω = 0) ∧
      (∀ ω ∈ G, ∀ t : ℝ≥0,
        ContinuousWithinAt (fun s : ℝ≥0 =>
          LevyFoundations.compoundPoisson (1 : ℝ) τ Y (s : ℝ) ω) (Ici t) t) ∧
      (∀ ω ∈ G, ∀ t : ℝ≥0, 0 < t →
        ∃ l, Tendsto (fun s : ℝ≥0 =>
          LevyFoundations.compoundPoisson (1 : ℝ) τ Y (s : ℝ) ω)
          (nhdsWithin t (Iio t)) (nhds l)) ∧
      (∀ ω ∈ G, ∀ t : ℝ≥0, ∀ l : ℝ, 0 < t →
        Tendsto (fun s : ℝ≥0 =>
          LevyFoundations.compoundPoisson (1 : ℝ) τ Y (s : ℝ) ω)
          (nhdsWithin t (Iio t)) (nhds l) →
        LevyFoundations.compoundPoisson (1 : ℝ) τ Y (t : ℝ) ω ≤ l) := by sorry
