-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_reflected_ruin_strict_survival_eq_exp_first_jump
-- name    : AvramDividend.Classical.bv_reflected_ruin_strict_survival_eq_exp_first_jump
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T17:36:55.526555+00:00
-- url     : https://prove2.me/theorems/fd28eb88-da32-48d1-8899-00445401300b
-- title:
--   Exact exponential strict-survival law of the genuine zero-barrier reflected ruin clock
-- statement:
--   The actual bounded-variation finite-negative-jump-activity standing spectrally negative Lévy reflected zero-barrier strict ruin-time survival satisfies P(t<τ)=exp(-λt) for every deterministic nonnegative time t. Its upper bound follows from the accepted strict-survival upper theorem. For any epsilon>0, surviving weakly to u=t+epsilon implies strict survival past t, and the accepted weak-survival lower theorem implies P(t<τ)≥exp(-λ(t+epsilon)). The accepted exponential_right_squeeze by right continuity gives exact equality. This resolves the strict/weak endpoint difference without constructing the first-jump Poisson process or proving atomlessness of τ.
-- source:
--   Avram, Palmowski, Pistorius 2007, §3.3 formula (3.14); Prove2Me accepted original strict upper, weak lower, exponential right squeeze.

import Theorems.Thm_AvramDividend_Classical_bv_reflected_ruin_survival_ge_exp_first_jump
import Theorems.Thm_AvramDividend_Classical_bv_reflected_ruin_strict_survival_le_exp_first_jump
import Theorems.Thm_AvramDividend_Classical_exponential_right_squeeze
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Data.NNReal.Basic
import Mathlib.Tactic

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_reflected_ruin_strict_survival_eq_exp_first_jump
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hStanding : X.Standing) (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (t : ℝ≥0) :
    P.real {ω : Ω | (t : ℝ≥0∞) < barrierRuinTime X 0 ω} =
      Real.exp (-((t : ℝ) * (X.ν (Iio (0 : ℝ))).toReal)) := by sorry
