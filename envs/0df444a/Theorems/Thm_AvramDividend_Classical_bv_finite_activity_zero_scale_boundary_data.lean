-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_finite_activity_zero_scale_boundary_data
-- name    : AvramDividend.Classical.bv_finite_activity_zero_scale_boundary_data
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T23:10:33.75837+00:00
-- url     : https://prove2.me/theorems/622d42b8-51ae-4d15-802c-b2f7dac98e2e
-- title:
--   Finite-activity bounded-variation scale-function value and right derivative at zero
-- statement:
--   The positive finite-variation drift d and finite negative-jump intensity lambda determine the scale-function boundary W(0)=1/d and the ordinary right derivative W'(0+)=(q+lambda)/d². Prove the scale data directly from the pinned Laplace-transform definition with appropriate Tauberian/renewal justification; the EReal liminf must match the ordinary limit.
-- source:
--   Avram, Palmowski and Pistorius (2007), scale zero-boundary formulas and Proposition 1, https://arxiv.org/pdf/math/0702893. The deterministic quotient lemma barrierValue_zero_of_finite_jump_normalisation is already Proved.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_finite_activity_zero_scale_boundary_data
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) :
    0 < X.drift ∧ W 0 = 1 / X.drift ∧
      derivZeroPlus W =
        (((q + (X.ν (Iio (0 : ℝ))).toReal) / X.drift ^ 2 : ℝ) : EReal) := by sorry
