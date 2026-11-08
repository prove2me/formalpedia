-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a19_affine_singular_global_positive_reserve_integrable
-- name    : AvramDividend.Classical.avram_a19_affine_singular_global_positive_reserve_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T17:48:32.130701+00:00
-- url     : https://prove2.me/theorems/835872b9-abd3-4de8-8787-b2ea3fabd63c
-- title:
--   Original singular Levy generator integrable at every strictly positive reserve
-- statement:
--   For the original source generator and singular negative-jump Levy density, the compensated jump integral is finite at each positive reserve by splitting at one.
-- source:
--   A19 original process generator; combines Proved small and large reserve predicates without strengthening the parent theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a19_affine_singular_original_generator_integrable
import Theorems.Thm_AvramDividend_Classical_avram_a19_affine_singular_large_reserve_generator_integrable
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a19_affine_singular_global_positive_reserve_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = volume.withDensity (fun z : ℝ =>
      if z ∈ Ioo (-1 : ℝ) 0
      then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0))
    (x : ℝ) (hx : 0 < x) :
    X.GeneratorIntegrable
      (fun u : ℝ => if u < 0 then (0 : ℝ) else 1 + u) x := by sorry
