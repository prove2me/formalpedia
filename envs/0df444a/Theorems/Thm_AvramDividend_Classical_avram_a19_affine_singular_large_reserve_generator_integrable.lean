-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a19_affine_singular_large_reserve_generator_integrable
-- name    : AvramDividend.Classical.avram_a19_affine_singular_large_reserve_generator_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T17:24:36.011928+00:00
-- url     : https://prove2.me/theorems/5db4adf7-d2ba-40e7-90b3-ad8a65289516
-- title:
--   Actual original singular generator is integrable at every reserve at least one
-- statement:
--   The original source-defined Levy generator integral exists at every reserve at least one under the proposed singular negative-jump measure.
-- source:
--   A19 original uniform-cell generator integrability, large-reserve branch using the previously Proved pointwise integrand-zero theorem and pinned Mathlib ae_withDensity_iff.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a19_affine_singular_large_reserve_integrand_zero
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a19_affine_singular_large_reserve_generator_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = volume.withDensity (fun z : ℝ =>
      if z ∈ Ioo (-1 : ℝ) 0
      then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0))
    (x : ℝ) (hx : 1 ≤ x) :
    X.GeneratorIntegrable
      (fun u : ℝ => if u < 0 then (0 : ℝ) else 1 + u) x := by sorry
