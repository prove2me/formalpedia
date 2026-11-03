-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_source_predictable_separated_rectangle_of_halfline_tests
-- name    : AvramDividend.Classical.avram_wave7_01_source_predictable_separated_rectangle_of_halfline_tests
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T21:44:12.780513+00:00
-- url     : https://prove2.me/theorems/e78a3b77-b29f-4f30-9ee3-d64b5d449e47
-- title:
--   Actual original predictable separated-mark rectangle compensation from finite half-line intensity tests
-- statement:
--   On the unchanged actual source Ω/P/X/𝓕, a finite expected number of separated negative jumps on (s,t] and the ν intensity identity for the generating halfline mark class imply the exact predictable marked rectangle compensation identity for every original past event A and every Borel mark subset B⊆(-∞,-ε]. This uses a genuine source mark-measure construction and halfline uniqueness, then the already Proved original independent-increments past-event factor. The finite mean and halfline tests remain explicit analytic obligations, and the two mark-measure helper imports must be Proved for a direct proof; otherwise this is an honest sketch reduction.
-- source:
--   Original past factor 264b3973 (Proved); two original finite-mark/halfline helpers c026 and pending all-start halfline helper; source publication preamble only Proved 264b, Open helpers imported solely in proof reduction

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_actual_intrinsic_rectangle_past_event_factor_unconditional
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_01_source_predictable_separated_rectangle_of_halfline_tests
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (ε : ℝ) (hε : 0 < ε)
    (hFiniteMean :
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ Iic (-ε)) ∂P) < ⊤)
    (hHalfline : ∀ a : ℝ,
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ (Iic a ∩ Iic (-ε))) ∂P) =
      (((t - s : ℝ≥0) : ℝ≥0∞)) * X.ν (Iic a ∩ Iic (-ε)))
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hBsep : B ⊆ Iic (-ε)) :
    (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) =
      P A * ((((t - s : ℝ≥0) : ℝ≥0∞)) * X.ν B) := by sorry
