-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gb42_centered_square_L2_implies_raw_fourth
-- name    : AvramDividend.Classical.avram_gb42_centered_square_L2_implies_raw_fourth
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T10:33:00.176205+00:00
-- url     : https://prove2.me/theorems/44122771-8845-4302-aceb-35b0fcad7b09
-- title:
--   An integrable centred quadratic square controls the raw fourth moment
-- statement:
--   On a probability space, if the square of Z squared minus a constant is integrable, then the raw fourth power of Z is integrable, with its expectation bounded by twice the centred-square second moment plus twice the squared constant. This is the exact algebraic moment transfer connecting the original Gaussian centred-square theorem gb41 with the bounded-coefficient theorem gb38.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical

theorem AvramDividend.Classical.avram_gb42_centered_square_L2_implies_raw_fourth
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → ℝ) (a : ℝ) (hZ : Measurable Z)
    (hc : Integrable (fun ω => ((Z ω) ^ 2 - a) ^ 2) P) :
    Integrable (fun ω => (Z ω) ^ 4) P ∧
      (∫ ω, (Z ω) ^ 4 ∂P) ≤
        2 * ((∫ ω, ((Z ω) ^ 2 - a) ^ 2 ∂P) + a ^ 2) := by
  sorry
