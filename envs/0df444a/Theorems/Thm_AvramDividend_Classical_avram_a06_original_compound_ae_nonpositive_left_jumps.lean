-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_original_compound_ae_nonpositive_left_jumps
-- name    : AvramDividend.Classical.avram_a06_original_compound_ae_nonpositive_left_jumps
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T22:58:14.938196+00:00
-- url     : https://prove2.me/theorems/4bdbe705-d4ea-4136-b8f7-691eed8858a5
-- title:
--   Original unit-drift compound Poisson has no positive jumps on one probability-one event
-- statement:
--   For a unit-rate driver with all marks in (-1,0), show on a single probability-one set that the original compound-Poisson path has no upward positive-time jump, for all times and any convergent left-limit witness. Use locally finite strictly increasing arrival times and negative jump marks. This is the last pathwise component of the source good-event lemma.
-- source:
--   Necessary root-connected subproblem of Avram A06 9a1ae714 good-event source.

import Mathlib
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
import Definitions.Def_levy_foundations_isCadlag
open MeasureTheory Set ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a06_original_compound_ae_nonpositive_left_jumps
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
    [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P) :
    ∀ᵐ ω ∂P, ∀ (t : ℝ≥0) (l : ℝ), 0 < t →
      Tendsto (fun s : ℝ≥0 =>
        LevyFoundations.compoundPoisson (1 : ℝ) τ Y (s : ℝ) ω)
        (nhdsWithin t (Iio t)) (nhds l) →
      LevyFoundations.compoundPoisson (1 : ℝ) τ Y (t : ℝ) ω ≤ l := by sorry
