-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_ruin_crossing_jump_integral_eq_tail_mass
-- name    : AvramDividend.Classical.avram_wave4_05_source_ruin_crossing_jump_integral_eq_tail_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T15:59:20.243375+00:00
-- url     : https://prove2.me/theorems/4fcc11a3-d70c-4211-bc84-57e04806e92f
-- title:
--   Exact Lévy ruin-crossing jump generator term equals negative candidate value times tail intensity
-- statement:
--   For a genuine source spectrally negative Lévy measure ν, arbitrary barrier-shaped W, and reserve x≥cstar+1, the ν-integral of the actual generator integrand over jumps y<−x which cross strictly below zero is exactly −vcstar W x multiplied by the Mathlib real measure (Measure.real) of that strict ruin-crossing tail. This proves the zero-reserve boundary term without treating it as zero, and retains the strict cut at y=−x, where the bounded-variation scale function may jump at reserve zero.
-- source:
--   Accepted full source compensated-jump kernel theorem, exact barrierValue zero branch, Mathlib setIntegral_congr_fun and set integral of real constant.

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_generatorIntegrand_far_field_exact_large_jump_kernel

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_05_source_ruin_crossing_jump_integral_eq_tail_mass
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (W : ℝ → ℝ) (x : ℝ)
    (hfar : (cstar W).toReal + 1 ≤ x) :
    (∫ y in Iio (-x),
      SpectrallyNegativeLevy.generatorIntegrand (vcstar W) x y ∂X.ν) =
      X.ν.real (Iio (-x)) * (-vcstar W x) := by sorry
