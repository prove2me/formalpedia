-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_scale_exponential_tilt_strict_positive
-- name    : AvramDividend.Classical.bv_scale_exponential_tilt_strict_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T09:26:45.208775+00:00
-- url     : https://prove2.me/theorems/d20de364-9305-495c-8c8c-501f3c86dd6a
-- title:
--   Positive exponential tilt of any bounded-variation q-scale function
-- statement:
--   Under Standing and BoundedVariation, the existing Proved scaleFunction_tilted_positive_monotone_of_bv theorem yields strict positivity of W^(q)(x) at each positive x. Multiplying by exp(-φx)>0 preserves positivity for every real φ. This isolates the positive-valued tilted scale function input needed by the logarithmic-derivative reconstruction.
-- source:
--   Proved AvramDividend.Classical.scaleFunction_tilted_positive_monotone_of_bv and Real.exp_pos.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_scale_exponential_tilt_strict_positive
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation) (φ : ℝ) :
    ∀ x : ℝ, 0 < x → 0 < Real.exp (-(φ * x)) * W x := by sorry
