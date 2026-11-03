-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_marked_future_measurable_extractor
-- name    : AvramDividend.Classical.avram_wave7_01_original_intrinsic_marked_future_measurable_extractor
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T12:55:42.019148+00:00
-- url     : https://prove2.me/theorems/5cf3e058-4372-4903-a4fe-24732496cb39
-- title:
--   Intrinsic marked original source count has a product-measurable same-future-path representation
-- statement:
--   Find a globally measurable functional on the coordinate product σ-algebra of all real-valued nonnegative-time paths that agrees on every actual SpectrallyNegativeLevy source path with its intrinsic marked jump count on (s,t]×B. The proved same-sample clock translation identifies the candidate count on càdlàg paths; measurable extension remains the hard task.
-- source:
--   Original shifted future count transport b1721778 and ed946858 when Proved; need rational cadlag approximations to get a Borel measurable extension.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_01_original_intrinsic_marked_future_measurable_extractor
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B) :
    ∃ F : (ℝ≥0 → ℝ) → ℝ≥0∞,
      Measurable F ∧
      (∀ ω : Ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) =
        F (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω)) := by sorry
