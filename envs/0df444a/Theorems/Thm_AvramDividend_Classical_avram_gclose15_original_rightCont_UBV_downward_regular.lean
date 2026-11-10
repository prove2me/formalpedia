-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gclose15_original_rightCont_UBV_downward_regular
-- name    : AvramDividend.Classical.avram_gclose15_original_rightCont_UBV_downward_regular
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T17:06:13.275198+00:00
-- url     : https://prove2.me/theorems/fae9d2c6-4970-410b-af4d-f0cc11e32e29
-- title:
--   Original unbounded-variation Levy path descends immediately after right-continuous filtration stopping times
-- statement:
--   At every genuine stopping clock for the right-continuous original filtration, an unbounded-variation spectrally negative Levy path has arbitrarily small strictly negative subsequent increments almost surely. The clock may be arbitrary and finite on every path. This transfers the proved finite-stopping downward regularity theorem through the proved same-path right-continuous Levy-process construction, preserving the exact original process rather than introducing an unproved auxiliary Brownian coupling.
-- source:
--   Direct source-exact bridge: Proved levy_rightCont_process 006d14c7 constructs a Levy structure on the original path at the right-continuous filtration with unchanged characteristic triplet; Proved avram_wave4_04_ubv_original_levy_finite_stopping_downward_regular_no_grid 66982d13 supplies downward regularity on that filtration. This removes the filtration mismatch for zero-contact and lower-corridor localisation on the root-connected Gaussian top branch 61cdc38d.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gclose15_original_rightCont_UBV_downward_regular
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (hstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0))) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ s : ℝ≥0, s < ε ∧
        X.X (τ ω + s) ω - X.X (τ ω) ω < 0 := by sorry
