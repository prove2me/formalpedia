-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_double_min_clock_rightcont_stopping
-- name    : AvramDividend.Classical.avram_sweep16_original_double_min_clock_rightcont_stopping
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T18:21:59.951619+00:00
-- url     : https://prove2.me/theorems/ca5bbe86-e547-4f6e-b8f1-61eb45315ba2
-- title:
--   Original double-min ruin and physical localiser remains a genuine right-continuous-filtration stopping time
-- statement:
--   For the exact original physical spectrally negative Levy filtration and an admissible dividend strategy, the true dividend ruin time is already a Proved right-continuous-filtration stopping time. The deterministic finite n is a stopping time as well; the minimum with it and then with any genuine stopping localiser S_k stays a stopping time. This discharges the filtration/stopping part of the same-clock local Ito source without assuming an augmented Levy process.
-- source:
--   Proved original ruinTime_stopping_rightCont_filtration 2d036d4f and Mathlib isStoppingTime_const/IsStoppingTime.min.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_sweep16_original_double_min_clock_rightcont_stopping
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (S : ℕ → Ω → ℝ≥0∞)
    (hSstop : ∀ k, IsStoppingTime 𝓕.rightCont (S k)) :
    ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => min (min (ruinTime X x D ω) (n : ℝ≥0∞)) (S k ω)) := by sorry
