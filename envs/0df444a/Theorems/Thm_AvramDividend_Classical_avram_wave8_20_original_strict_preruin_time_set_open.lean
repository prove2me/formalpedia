-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_strict_preruin_time_set_open
-- name    : AvramDividend.Classical.avram_wave8_20_original_strict_preruin_time_set_open
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:24:14.536516+00:00
-- url     : https://prove2.me/theorems/46f81399-0ec6-46bd-9245-4a2eb4eeba00
-- title:
--   Original source strict pre-ruin physical-time set is pathwise open
-- statement:
--   On every original source sample path, times strictly before its actual ruin time form an open subset of nonnegative physical time. Any strictly surviving stopping time therefore has a genuine right neighbourhood of surviving times. The claim is topological and independent of HJB/generator estimates, negative overshoots, or admissibility at ruin.
-- source:
--   Original Avram ruinTime source and exact embedding of physical NNReal clocks into ENNReal. The strict survival domain is the continuous inverse image of Iio ruinTime under ENNReal.ofNNReal. It is open even when ruinTime=top or when ruin occurs by creeping or jump. This supports choosing right neighbourhoods in W8-04 without replacing strict survival by closed survival.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave8_20_original_strict_preruin_time_set_open
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < ruinTime X x D ω} := by sorry
