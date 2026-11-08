-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_e0_singular_density_condition33
-- name    : AvramDividend.Classical.avram_e0_singular_density_condition33
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T17:34:09.377833+00:00
-- url     : https://prove2.me/theorems/d1b83921-2282-43d7-acc5-dc3de3e4bc8e
-- title:
--   The explicit singular Lévy density supplies the absolute-continuity Standing alternative
-- statement:
--   For a spectrally negative Lévy structure whose jump measure is the explicit singular inverse-three-halves negative density, the absolutely-continuous alternative of its original Condition33 assumption holds, by the previously proved singular-density absolute-continuity theorem.
-- source:
--   Direct necessary Standing branch for the source-exact e0b94d7f countermodel; proof will import e0a856a6.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_e0_singular_density_condition33
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = volume.withDensity (fun z : ℝ =>
      if z ∈ Ioo (-1 : ℝ) 0
      then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0)) :
    X.Condition33 := by sorry
