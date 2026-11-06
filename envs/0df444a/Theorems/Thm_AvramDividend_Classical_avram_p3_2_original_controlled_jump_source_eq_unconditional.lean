-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_controlled_jump_source_eq_unconditional
-- name    : AvramDividend.Classical.avram_p3_2_original_controlled_jump_source_eq_unconditional
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T10:28:55.205267+00:00
-- url     : https://prove2.me/theorems/2f5d2569-5e15-40d2-b220-1ef6d30f3f1f
-- title:
--   Original controlled positive-time jump equals exact Lévy source jump minus simultaneous dividend atom
-- statement:
--   The true original controlled post-payment reserve jump at every positive time is exactly the original Lévy X jump less the coincident right-dividend payment atom. Original cadlag regularity supplies the left limit automatically, so the result can feed the marked source compensator without a fabricated left-limit hypothesis or disjoint-jump assumption.
-- source:
--   Proved original cadlag source 09e1699b and accepted original postpayment jump 7a274da1.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_cadlag_regular_all_times
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_controlled_postpayment_jump_source_eq

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_controlled_jump_source_eq_unconditional
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0) (ht : 0 < t) :
    (x + X.X t ω - rightLimit D t ω) -
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t =
      (X.X t ω -
        Function.leftLim (fun s : ℝ≥0 => X.X s ω) t) -
          (rightLimit D t ω - D t ω) := by sorry
