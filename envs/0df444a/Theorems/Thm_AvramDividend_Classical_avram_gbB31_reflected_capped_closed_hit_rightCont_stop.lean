-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB31_reflected_capped_closed_hit_rightCont_stop
-- name    : AvramDividend.Classical.avram_gbB31_reflected_capped_closed_hit_rightCont_stop
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T17:58:18.790853+00:00
-- url     : https://prove2.me/theorems/64e36151-3e75-4859-a7d0-4d2709b50b84
-- title:
--   Original reflected capped first closed hit is stopping time for right-continuous filtration
-- statement:
--   Use the already Proved original reflected supremum capped first closed hitting stopping-time theorem and the inclusion of any filtration into its right-continuous enlargement to obtain exactly the stopping-time property needed by Gaussian stopped physical-grid sources.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_reflectedSup_capped_firstClosedHit_isStoppingTime
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB31_reflected_capped_closed_hit_rightCont_stop
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (S : Set ℝ≥0) (hS : S.Countable) (hDense : Dense S)
    (h0 : (0 : ℝ≥0) ∈ S)
    (H : ℝ≥0) (x : ℝ) :
    IsStoppingTime 𝓕.rightCont (fun ω : Ω =>
      WithTop.some (sInf ((Icc (0 : ℝ≥0) H ∩
        (fun u : ℝ≥0 => reflectedSup X u ω) ⁻¹' Ici x) ∪ {H}))) := by sorry
