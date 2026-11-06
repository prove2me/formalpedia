-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_random_two_reserve_negative_mark_joint_L2_difference
-- name    : AvramDividend.Classical.avram_p4_f3_original_random_two_reserve_negative_mark_joint_L2_difference
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:14:16.060767+00:00
-- url     : https://prove2.me/theorems/9a4e6c54-688d-4689-b2be-a57b7511602c
-- title:
--   Original joint negative-mark quadratic difference energy for two random stopped reserve states
-- statement:
--   For two random capital states confined to the same compact positive reserve band, the difference of their physical original negative-mark value jump coefficients has finite joint quadratic energy under the same original probability P and Lévy ν.
-- source:
--   Use Proved two-state min(1,z²) domination and X.ν_integrable, followed by monotone physical ν and P lintegrals. Supports finite-energy side of predictable grid approximation without treating grid convergence as established.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_negative_mark_two_state_squared_difference_dominated
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original random-state coefficient differences have finite joint quadratic Levy energy. -/

theorem AvramDividend.Classical.avram_p4_f3_original_random_two_reserve_negative_mark_joint_L2_difference
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (δ K : ℝ) (hδ : 0 < δ) (hδK : δ ≤ K)
    (hK : ENNReal.ofReal K < C)
    (U V : Ω → ℝ)
    (hU : ∀ ω, U ω ∈ Icc δ K)
    (hV : ∀ ω, V ω ∈ Icc δ K) :
    (∫⁻ ω, (∫⁻ z in Iio (0 : ℝ),
      ENNReal.ofReal
        (((w (U ω + z) - w (U ω)) -
          (w (V ω + z) - w (V ω))) ^ 2) ∂X.ν) ∂P) < ⊤ := by sorry
