-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB30_zerojump_local_affine_jet_generator_drift
-- name    : AvramDividend.Classical.avram_gbB30_zerojump_local_affine_jet_generator_drift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T13:17:39.916937+00:00
-- url     : https://prove2.me/theorems/d243cbb2-3b48-4b50-a5d2-329b5596ab6d
-- title:
--   Zero-jump Gaussian generator of any locally unit-affine jet equals drift
-- statement:
--   For a zero-jump spectrally negative Levy source, any test function with first derivative one and second iterated derivative zero at a point has a generator integrable there, with generator equal to the source drift. This applies above an interior cap-linear clipping threshold even though the test function is not globally affine.
-- source:
--   The Proved zero-jump Gaussian pointwise generator identity and integrability under zero Levy measure.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f11_zero_jump_generator_eq_gaussian_drift
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB30_zerojump_local_affine_jet_generator_drift
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (V : ℝ → ℝ) (y : ℝ)
    (hfirst : deriv V y = 1)
    (hsecond : iteratedDeriv 2 V y = 0) :
    X.GeneratorIntegrable V y ∧ X.generator V y = X.c := by sorry
