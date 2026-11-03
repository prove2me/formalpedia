-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_empty_mark_predictable_rectangle
-- name    : AvramDividend.Classical.avram_wave7_01_original_empty_mark_predictable_rectangle
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T12:32:07.042004+00:00
-- url     : https://prove2.me/theorems/1176284f-355e-45aa-ae29-f622622a1661
-- title:
--   Original intrinsic predictable marked rectangle has exact zero mass for the empty mark set
-- statement:
--   For the unchanged original SpectrallyNegativeLevy process and its own filtration, the precise target rectangle compensation formula is valid for the empty Borel mark set, for any deterministic interval and any original past event. The identity follows because the source jump measure of a Cartesian product with empty mark set is zero and ν(∅)=0. It assumes neither BV, finite Lévy activity nor a measurable future-path extractor.
-- source:
--   Exact zero-mark boundary case of canonical predictable rectangle compensator 393b03a8-2e9a-43d8-b415-854d86d58104; original source expression and original filtration preserved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_01_original_empty_mark_predictable_rectangle
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A) :
    (∫⁻ ω in A,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ (∅ : Set ℝ)) ∂P) =
    P A * ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (∅ : Set ℝ) := by sorry
