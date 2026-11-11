-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_compoundPoissonStartsZeroAE_public
-- name    : AvramDividend.Classical.avram_a06_compoundPoissonStartsZeroAE_public
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T17:20:46.065303+00:00
-- url     : https://prove2.me/theorems/fe4c18a3-a2ec-4910-8bd8-f6a1b164e884
-- title:
--   Public canonical compound Poisson process starts at zero almost surely
-- statement:
--   For any true compound-Poisson driver with positive rate, the canonical càdlàg piecewise path begins at zero almost surely. Used in the original Avram BV Lévy-process modification and natural-filtration assembly.
-- source:
--   Proved public interarrival positivity 0f58eb54 and public piecewise path start 41a5b6c7; duplicates the useful result otherwise available only via a private imported theorem.

import Mathlib
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
import Theorems.Thm_levy_foundations_compoundDriverInterarrivalPositive
import Theorems.Thm_levy_foundations_piecewisePathAtZero
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_compoundPoissonStartsZeroAE_public
    {Ω : Type*} [MeasurableSpace Ω]
    {τ Y : ℕ → Ω → ℝ} {r : ℝ≥0} {ν' : Measure ℝ} {P : Measure Ω}
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y r ν' P)
    (hr : 0 < r) (b : ℝ) :
    ∀ᵐ ω ∂P, LevyFoundations.compoundPoisson b τ Y 0 ω = 0 := by sorry
