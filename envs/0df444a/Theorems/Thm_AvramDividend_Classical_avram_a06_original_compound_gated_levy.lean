-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_original_compound_gated_levy
-- name    : AvramDividend.Classical.avram_a06_original_compound_gated_levy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T23:26:20.991567+00:00
-- url     : https://prove2.me/theorems/134fa523-3011-46a2-b939-4c9c4b2bcbf2
-- title:
--   Original compound-Poisson driver has Lévy increments after full-measure zero-start gating
-- statement:
--   The original marked compound-Poisson process, gated outside an arbitrary measurable probability-one zero-start event, satisfies the full Lévy-process axioms. A DecidablePred instance is included to elaborate the conditional in the declaration.
-- source:
--   A06 corrected original same-space source decomposition, repaired statement after publication error E Decidable (ω∈G).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory Set ProbabilityTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_original_compound_gated_levy
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
    [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P)
    (G : Set ((ℕ → ℝ) × (ℕ → ℝ)))
    [DecidablePred (fun ω => ω ∈ G)]
    (hGmeas : MeasurableSet G)
    (hGae : ∀ᵐ ω ∂P, ω ∈ G)
    (hGzero : ∀ ω ∈ G,
      LevyFoundations.compoundPoisson (1 : ℝ) τ Y 0 ω = 0) :
    IsLevyProcess
      (fun (t : ℝ≥0) ω =>
        if ω ∈ G then LevyFoundations.compoundPoisson (1 : ℝ) τ Y (t : ℝ) ω
        else (0 : ℝ)) P := by sorry
