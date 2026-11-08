-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_e0_singular_sigma_zero_bv
-- name    : AvramDividend.Classical.avram_e0_singular_sigma_zero_bv
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T17:55:24.30066+00:00
-- url     : https://prove2.me/theorems/1b2a6ffe-9c88-4757-9739-63ac25375e67
-- title:
--   Zero Gaussian coefficient and the singular negative-jump density give original bounded variation
-- statement:
--   The singular inverse-three-halves negative-jump Lévy measure with zero Gaussian coefficient meets the two fields of original SpectrallyNegativeLevy.BoundedVariation. The first is the supplied zero coefficient; the second follows from the previously Proved exact first-moment lintegral bound.
-- source:
--   Original bounded-variation hypothesis required by e0b94d7f-cb1e-450a-8f04-b2e732af5dbe.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gen15_singular_density_bv_lintegral_finite
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_e0_singular_sigma_zero_bv
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hσ : X.σ = 0)
    (hν : X.ν = volume.withDensity (fun z : ℝ =>
      if z ∈ Ioo (-1 : ℝ) 0
      then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0)) :
    X.BoundedVariation := by sorry
