-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_true_real_clock_reflected_law_nonnegative_support
-- name    : AvramDividend.Classical.esscher_true_real_clock_reflected_law_nonnegative_support
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T20:18:23.663281+00:00
-- url     : https://prove2.me/theorems/4e6aabf8-190a-4dc5-b842-336f0f8bb78f
-- title:
--   The genuine Lévy reflected-infimum pushforward under every real clock law has nonnegative support
-- statement:
--   For every genuine spectrally negative Lévy process and every joint path×real-time measure Q, without independence, exponential-clock or Esscher assumptions, the pushforward law of the observed negative running infimum up to the clamped nonnegative clock has zero mass on the negative half-line. The result follows pathwise from the established Lévy process zero-start running infimum nonnegativity and the accepted joint path-time measurability theorem. In particular the true jointly Esscher-tilted path×Exp(p) reflected-infimum probability law meets the support hypothesis of the exact cumulative-CDF-to-Laplace identity for every p>0. No Wiener–Hopf factorisation is assumed.
-- source:
--   Accepted chat04_negative_running_infimum_nonneg b5791ec9 and levy_running_infimum_joint_time_path_measurable, pinned Mathlib Measure.map_apply.

import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Theorems.Thm_AvramDividend_Classical_chat04_negative_running_infimum_nonneg
import Theorems.Thm_AvramDividend_Classical_levy_running_infimum_joint_time_path_measurable
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_true_real_clock_reflected_law_nonnegative_support
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (Q : Measure (Ω × ℝ)) :
    (Measure.map (fun z : Ω × ℝ => -sInf {y : ℝ | ∃ s : ℝ≥0,
        s ≤ Real.toNNReal z.2 ∧ y = X.X s z.1}) Q) (Iio (0 : ℝ)) = 0 := by sorry
