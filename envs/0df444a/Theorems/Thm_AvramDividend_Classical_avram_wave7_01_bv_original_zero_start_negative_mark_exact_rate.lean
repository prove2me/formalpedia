-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_bv_original_zero_start_negative_mark_exact_rate
-- name    : AvramDividend.Classical.avram_wave7_01_bv_original_zero_start_negative_mark_exact_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T15:32:06.692618+00:00
-- url     : https://prove2.me/theorems/da7b127b-7afe-429f-9906-dee7b44d2999
-- title:
--   Actual BV finite-activity negative-jump intensity includes the initial time-zero clock
-- statement:
--   For the exact original bounded-variation spectrally negative Lévy process with explicit finite negative Lévy intensity, prove E_P N_X((0,T]×(-∞,0)) = T ν((−∞,0)) for every positive T. This fills the s=0 endpoint omitted from the prior strictly positive-start negative-mark theorem. It uses source pathwise negative support and the already Proved original total jump intensity at initial horizons, without a replacement Poisson process.
-- source:
--   Combine Proved original BV total first-moment at (0,T]×ℝ 4d7761f5-1504-4355-8d1b-8fa6d57926f1 with exact pathwise mark restriction c2e1a7f1-1187-4e21-9384-0ae2531dc181.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_bv_original_total_jump_intensity_gridfree
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_arbitrary_mark_negative_support_count

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_01_bv_original_zero_start_negative_mark_exact_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) (hT : 0 < T) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ Iio (0 : ℝ)) ∂P) =
      (T : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) := by sorry
