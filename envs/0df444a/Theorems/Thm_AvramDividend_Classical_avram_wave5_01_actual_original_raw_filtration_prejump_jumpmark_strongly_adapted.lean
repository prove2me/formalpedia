-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_original_raw_filtration_prejump_jumpmark_strongly_adapted
-- name    : AvramDividend.Classical.avram_wave5_01_actual_original_raw_filtration_prejump_jumpmark_strongly_adapted
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T08:56:12.53254+00:00
-- url     : https://prove2.me/theorems/73fbc493-27da-4bef-ac31-f2b41adf1102
-- title:
--   Genuine source prejump and jump mark strongly adapted to the raw original filtration
-- statement:
--   For every original SpectrallyNegativeLevy P 𝓕, both the genuine left-limit process and original jump-mark process are strongly adapted to the raw source filtration 𝓕 itself, without replacing it by 𝓕.rightCont or adding a completed filtration. The proof instantiates the Proved general left-limit-adaptedness theorem with X.adapted and X.leftLim on the same Ω. No BV, intensity or Poisson copy is required.
-- source:
--   Generic strongly adapted left-limit theorem 4a78651d and the actual original X.adapted and X.leftLim source fields.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_stronglyAdapted_leftLim_of_exists_leftLimits

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_01_actual_original_raw_filtration_prejump_jumpmark_strongly_adapted
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    StronglyAdapted 𝓕
      (fun t ω => Function.leftLim (fun s : ℝ≥0 => X.X s ω) t) ∧
    StronglyAdapted 𝓕
      (fun t ω => X.X t ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) t) := by sorry
