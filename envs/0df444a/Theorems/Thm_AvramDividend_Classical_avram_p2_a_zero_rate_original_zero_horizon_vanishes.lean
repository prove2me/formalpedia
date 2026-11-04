-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_zero_horizon_vanishes
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_original_zero_horizon_vanishes
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T13:30:40.291281+00:00
-- url     : https://prove2.me/theorems/660f2515-9695-40bf-ba41-d99186552ffb
-- title:
--   Original Lévy zero-horizon marked jump expectation is exactly zero
-- statement:
--   On the genuine source Levy process and probability space, no strictly positive jump time lies in the empty interval (0,0]. Therefore the intrinsic marked count of any B in that zero-horizon rectangle vanishes and so does its ENNReal expectation, even for unbounded B, without a compensator, source-law assumption or finiteness condition.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_a_zero_rate_original_zero_horizon_vanishes
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (B : Set ℝ) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
       X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
       (fun u : ℝ≥0 => (u,
         X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
       (Ioc 0 0 ×ˢ B) ∂P) = 0 := by sorry
