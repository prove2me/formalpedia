-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_compoundPoissonCadlagAE_public
-- name    : AvramDividend.Classical.avram_a06_compoundPoissonCadlagAE_public
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T17:07:35.445482+00:00
-- url     : https://prove2.me/theorems/f2fa1a19-c98e-4746-bfd5-281eb64683d6
-- title:
--   Public almost-sure cadlag regularity of compound-Poisson paths with drift
-- statement:
--   For a jointly independent compound-Poisson driver, almost every drift-plus-jump path is right-continuous with left limits. Strictly increasing and divergent arrival times hold almost surely, and the existing public deterministic piecewise-path theorem proves all-path cadlag on that event. Supplies the publicly reusable path regularity required by the A06 original filtered BV source adapter.
-- source:
--   Public source-exact transplant of LeanLevy CompoundPoisson.lean lines 339-342. Independent of formerly private compoundPoissonCadlagAE. Root-connected A06 adapter child avram_a06_bv_compound_driver_to_original_source.

import Mathlib
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
import Theorems.Thm_levy_foundations_compoundDriverArrivalStrictMono
import Theorems.Thm_levy_foundations_compoundDriverArrivalDiverges
import Theorems.Thm_levy_foundations_piecewisePathIsCadlag
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_compoundPoissonCadlagAE_public
    {Ω : Type*} [MeasurableSpace Ω]
    {τ Y : ℕ → Ω → ℝ} {r : ℝ≥0} {ν' : Measure ℝ} {P : Measure Ω}
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y r ν' P)
    (hr : 0 < r) (b : ℝ) :
    ∀ᵐ ω ∂P,
      LevyFoundations.isCadlag
        (fun t => LevyFoundations.compoundPoisson b τ Y t ω) := by sorry
