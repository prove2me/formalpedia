-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a19_affine_singular_original_generator_integrable
-- name    : AvramDividend.Classical.avram_a19_affine_singular_original_generator_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T16:30:56.360942+00:00
-- url     : https://prove2.me/theorems/260391b2-9245-4dac-a36c-758e2d97a806
-- title:
--   Actual original generator integrability under the singular negative Levy measure
-- statement:
--   The original Levy generator integrability predicate holds for the zero-extended affine value candidate at every positive subunit reserve when the process has the singular negative jump measure.
-- source:
--   Direct original-process predicate interface from public Proved avram_gen15_affine_singular_generator_jump_integrable, for A19 singular countermodel analysis.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gen15_affine_singular_generator_jump_integrable
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a19_affine_singular_original_generator_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = volume.withDensity (fun z : ℝ =>
      if z ∈ Ioo (-1 : ℝ) 0
      then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0))
    (x : ℝ) (hx : 0 < x) (hcap : x < 1) :
    X.GeneratorIntegrable
      (fun u : ℝ => if u < 0 then (0 : ℝ) else 1 + u) x := by sorry
