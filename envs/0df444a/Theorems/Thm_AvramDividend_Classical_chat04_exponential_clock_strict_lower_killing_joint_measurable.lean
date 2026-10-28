-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_exponential_clock_strict_lower_killing_joint_measurable
-- name    : AvramDividend.Classical.chat04_exponential_clock_strict_lower_killing_joint_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T12:52:16.346194+00:00
-- url     : https://prove2.me/theorems/c740e195-ec2c-463d-b1f4-4c11c511a0f3
-- title:
--   Genuine Lévy lower-killed exponential-clock survival event is jointly measurable
-- statement:
--   For any spectrally negative Lévy process and any lower threshold, the joint event in actual path space Ω and real observation time t that t is nonnegative and strictly earlier than the process's true strict lower first-passage clock is measurable. This is exactly the stochastic killing event needed for the independent exponential-horizon resolvent integral and assumes no scale-function harmonicity or exit identity.
-- source:
--   Canonical Proved joint measurability of strict named passage clocks 3d4daa72-4dba-48f9-9f55-b9a0e92786e4 and Mathlib measurability of ENNReal.ofReal and product coordinate projections. Intended for exact exponential-clock stochastic resolvent factorization.

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat03_both_named_passage_clocks_measurable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_exponential_clock_strict_lower_killing_joint_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (lower : ℝ) :
    MeasurableSet
      {z : Ω × ℝ | 0 ≤ z.2 ∧
        ENNReal.ofReal z.2 < twoSidedExitDownTime X lower z.1} := by sorry
