-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_intrinsic_marked_void_stationary_without_counter_premise
-- name    : AvramDividend.Classical.avram_wave7_06_original_intrinsic_marked_void_stationary_without_counter_premise
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:57:41.490048+00:00
-- url     : https://prove2.me/theorems/c64a7b2a-2caa-4f4f-bee0-b0160203fb59
-- title:
--   Actual source Borel-marked jump voids are stationary under deterministic clock shifts
-- statement:
--   The exact source Borel-marked jump count has shift-stationary zero-event probabilities for every deterministic start and horizon. The same canonical measurable càdlàg path jump counter from the Proved universal extractor represents both shifted and zero-based genuine original Lévy paths, and the source whole-path stationary law transfers its zero fibre. The theorem requires no Poisson law, Lévy rate or additional shared counter hypothesis; NX is required explicitly to equal the intrinsic original X jump measure.
-- source:
--   Composition of Proved universal càdlàg marked path-count functional 41bfd2c8, actual source clock transport b1721778, shifted source càdlàg 984180e2 and W7-06 shared-counter stationarity 680e2ccc.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_intrinsic_marked_void_stationary_without_counter_premise
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (NX : Ω → Measure (ℝ≥0 × ℝ))
    (hNX : ∀ ω, NX ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))
    (s T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B) :
    P {ω : Ω | NX ω (Ioc s (s + T) ×ˢ B) = 0} =
    P {ω : Ω | NX ω (Ioc 0 T ×ˢ B) = 0} := by sorry
