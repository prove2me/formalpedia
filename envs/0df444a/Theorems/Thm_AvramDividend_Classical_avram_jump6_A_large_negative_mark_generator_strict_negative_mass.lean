-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_A_large_negative_mark_generator_strict_negative_mass
-- name    : AvramDividend.Classical.avram_jump6_A_large_negative_mark_generator_strict_negative_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T18:32:10.899387+00:00
-- url     : https://prove2.me/theorems/d82f6b91-a816-4061-8e02-19592261e7c1
-- title:
--   Strictly negative genuine generator compensator for positive finite overshooting jump intensity
-- statement:
--   For finite genuinely negative jump intensity, supported on marks at most minus two, the original quadratic capped HJB nonlinear generator integral is strictly negative at reserves from zero to one fifth whenever the negative mark intensity has positive real mass. This preserves the genuine marked nonlinear compensator in the ruin-clipped Itô ledger.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_A_large_negative_mark_generator_strict_negative_mass
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hSupport : ∀ᵐ z ∂(X.ν.restrict (Iio (0 : ℝ))), z ≤ -2)
    (hMass : 0 < (X.ν (Iio (0 : ℝ))).toReal)
    (y : ℝ) (hy : 0 ≤ y) (hcap : y ≤ 1 / 5) :
    (∫ z in Iio (0 : ℝ),
      SpectrallyNegativeLevy.generatorIntegrand
        (fun u : ℝ => if u < 0 then 0 else 1 + u + u ^ 2)
        y z ∂X.ν) < 0 := by sorry
