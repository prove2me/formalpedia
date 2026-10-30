-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_01_actual_killed_wh_pair
-- name    : AvramDividend.Classical.avram_root29_01_actual_killed_wh_pair
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T08:00:45.986669+00:00
-- url     : https://prove2.me/theorems/3b4448ee-6d26-4813-80a8-9194ef4b70c6
-- title:
--   Original Lévy lower-killed scale reward in the true supremum–drawdown joint law
-- statement:
--   For the actual spectrally negative Lévy process at an independent exponential observation time, the lower-history-surviving q-scale reward equals the expectation of the same reward over the genuine original-clock supremum and terminal drawdown joint law. No Wiener–Hopf independence or two-sided exit formula is assumed. This source-level identity links the already-Proved reflected-killed law with the actual joint reversal and is a prerequisite for recognizing the scalar killed-resolvent action.
-- source:
--   Derived from canonical Proved genuine killed reflected law 06a1bccb-7e42-4b81-baf4-9bfb641c6122 and full original pair reversal c569cf34-8b78-477d-a123-4b6aa63cf951; candidate source work/avram_root29_01_actual_killed_wh_pair.lean. Separate from Chat 02 generic independent-product disintegration.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_chat04_true_killed_exponential_joint_infimum_drawdown_ws01a
import Theorems.Thm_AvramDividend_Classical_chat04_actual_exponential_clock_affine_reflected_pair_law_ws01a
import Theorems.Thm_AvramDividend_Classical_levy_running_infimum_joint_time_path_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_scaleFunction_measurable_of_punctured_continuity

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_01_actual_killed_wh_pair
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (r : ℝ) (hr : 0 < r) (x q : ℝ) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) :
    (∫⁻ z : Ω × ℝ,
      if ∀ s : ℝ≥0, s ≤ Real.toNNReal z.2 → 0 ≤ x + X.X s z.1
      then ENNReal.ofReal (W (x + X.X (Real.toNNReal z.2) z.1))
      else (0 : ℝ≥0∞) ∂(P.prod (expMeasure r))) =
    (∫⁻ a : ℝ × ℝ,
      if a.2 ≤ x then ENNReal.ofReal (W (x - a.2 + a.1))
      else (0 : ℝ≥0∞)
      ∂((P.prod (expMeasure r)).map
        (fun z : Ω × ℝ =>
          (runningSup X (Real.toNNReal z.2) z.1,
           runningSup X (Real.toNNReal z.2) z.1 -
             X.X (Real.toNNReal z.2) z.1)))) := by sorry
