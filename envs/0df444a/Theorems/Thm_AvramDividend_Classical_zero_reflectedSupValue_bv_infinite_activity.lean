-- Prove2me | Theorems.Thm_AvramDividend_Classical_zero_reflectedSupValue_bv_infinite_activity
-- name    : AvramDividend.Classical.zero_reflectedSupValue_bv_infinite_activity
-- status  : Open
-- author  : @WillR
-- created : 2026-10-25T23:02:44.997693+00:00
-- url     : https://prove2.me/theorems/625fac59-bc0e-4cbb-b9c7-219536136b68
-- title:
--   Zero reflected valuation from infinite negative-jump intensity
-- statement:
--   For bounded-variation Lévy processes with infinite negative-jump activity and finite negative-jump first moment, arbitrary early negative jumps force instantaneous zero-barrier ruin, while the zero-barrier scale right derivative is infinite, so both reflected reward and scale boundary candidate vanish.
-- source:
--   Avram, Palmowski and Pistorius (2007), §3.3, with the source-faithful small-time ν estimate described in artifacts/mission_research/1300fbe7-ca8c-49f9-a4de-4cb35ebd2f43/latest.md. Proved conditional identity zero_reflectedSupValue_of_ae_early_downward_jumps_and_deriv_top (9228cae3).

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.zero_reflectedSupValue_bv_infinite_activity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (hInfinite : ¬ X.ν (Iio (0 : ℝ)) < ⊤) :
    barrierSupValue X 0 q = ENNReal.ofReal (barrierValue W 0 0) := by sorry
