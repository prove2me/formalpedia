-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_finite_activity_zero_reflected_first_jump_payout
-- name    : AvramDividend.Classical.bv_finite_activity_zero_reflected_first_jump_payout
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T23:10:41.056731+00:00
-- url     : https://prove2.me/theorems/6f73f927-fef3-4f1f-be8d-8c1e8e24f34c
-- title:
--   Finite-activity zero-reflection payout law up to the first negative jump
-- statement:
--   In the bounded-variation finite-intensity case, the positive canonical drift is continuously reflected into dividends until the first strictly negative jump, whose law has rate lambda equal to the total negative-jump Lévy mass. The expected discounted drift payout equals d/(q+lambda). Establish the stopped Stieltjes payout identity from the exact process axioms.
-- source:
--   Avram, Palmowski and Pistorius (2007), finite-activity case of Proposition 1, equation (3.14), https://arxiv.org/pdf/math/0702893. Main missing ingredient is the law of the first negative jump and identification of the dividend Stieltjes measure before ruin.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_finite_activity_zero_reflected_first_jump_payout
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) :
    barrierSupValue X 0 q =
      ENNReal.ofReal (X.drift / (q + (X.ν (Iio (0 : ℝ))).toReal)) := by sorry
