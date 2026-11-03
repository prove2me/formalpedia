-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_borel_marked_unconditional_levy_rate
-- name    : AvramDividend.Classical.avram_wave7_01_original_intrinsic_borel_marked_unconditional_levy_rate
-- status  : Open
-- author  : @WillR
-- created : 2026-11-02T12:55:57.713486+00:00
-- url     : https://prove2.me/theorems/859bf7be-1e5d-40c6-98fa-b438f19735af
-- title:
--   Original intrinsic marked Lévy jump measure has unconditional arbitrary Borel rate
-- statement:
--   For the exact original SpectrallyNegativeLevy probability measure P, prove the expected number of all literal jumps with marks in arbitrary Borel B on (s,t] equals (t-s)ν(B), including infinite activity and initial time. No finite-activity assumption is hidden, and count can equal ⊤.
-- source:
--   Proved original expected time–mark measure e509ef60, source small-time derivative e6973988 and finite-band moment identities should identify the Lévy measure.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_01_original_intrinsic_borel_marked_unconditional_levy_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) =
      ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B := by sorry
