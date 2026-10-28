-- Prove2me | Theorems.Thm_AvramDividend_Classical_zero_reflectedSupValue_bv_finite_activity
-- name    : AvramDividend.Classical.zero_reflectedSupValue_bv_finite_activity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T23:02:45.682099+00:00
-- url     : https://prove2.me/theorems/cd185c75-d541-4e4d-9571-b22448c4c714
-- title:
--   Zero reflected valuation from finite negative-jump intensity
-- statement:
--   For bounded-variation Lévy processes with finite negative-jump intensity, calculate the discounted reflected payout up to the first ruin-inducing jump and identify it with the finite right-slope scale normalisation at zero. Standing rules out the monotone pure-drift degenerate case.
-- source:
--   Avram, Palmowski and Pistorius (2007), §3.3. The already Proved barrierValue_zero_of_finite_jump_normalisation (73b88d8e) supplies the analytic final quotient given the scale origin and right derivative. The stochastic first-jump payout law remains the main proof obligation.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.zero_reflectedSupValue_bv_finite_activity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) :
    barrierSupValue X 0 q = ENNReal.ofReal (barrierValue W 0 0) := by sorry
