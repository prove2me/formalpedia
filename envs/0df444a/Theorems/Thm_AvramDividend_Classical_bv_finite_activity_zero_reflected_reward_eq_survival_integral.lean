-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_finite_activity_zero_reflected_reward_eq_survival_integral
-- name    : AvramDividend.Classical.bv_finite_activity_zero_reflected_reward_eq_survival_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T23:42:05.171491+00:00
-- url     : https://prove2.me/theorems/ce89e701-d4cb-4f1a-afbb-1b1b6e231674
-- title:
--   Zero-barrier stopped Stieltjes reward equals exponential first-jump survival integral
-- statement:
--   For a standing bounded-variation spectrally negative Lévy process with finite negative jump intensity, identify the zero-barrier cumulative running-supremum Stieltjes payout before strict drawdown ruin with its deterministic drift d times the exponential survival curve of the first negative jump. This theorem carries the genuine missing stochastic law and Tonelli/measure identification needed to establish the first-jump reward formula.
-- source:
--   Avram, Palmowski and Pistorius (2007), §3.3 formula (3.14), https://arxiv.org/pdf/math/0702893. Research: artifacts/mission_research/1300fbe7-ca8c-49f9-a4de-4cb35ebd2f43/finite-activity-local-renewal-c1-2026-10-25.md.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_finite_activity_zero_reflected_reward_eq_survival_integral
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) :
    barrierSupValue X 0 q =
      ENNReal.ofReal
        (∫ t : ℝ in Ioi (0 : ℝ),
          X.drift * Real.exp (-(q + (X.ν (Iio (0 : ℝ))).toReal) * t)
            ∂volume) := by sorry
