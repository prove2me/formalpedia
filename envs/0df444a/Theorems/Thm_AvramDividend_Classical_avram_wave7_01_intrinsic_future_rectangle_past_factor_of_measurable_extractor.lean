-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_intrinsic_future_rectangle_past_factor_of_measurable_extractor
-- name    : AvramDividend.Classical.avram_wave7_01_intrinsic_future_rectangle_past_factor_of_measurable_extractor
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T11:46:57.922192+00:00
-- url     : https://prove2.me/theorems/ad24b83b-aa01-4fe1-a792-380fdb3e7329
-- title:
--   Actual Lévy future marked jump count factors from every original past event once its path extractor is measurable
-- statement:
--   For the actual SpectrallyNegativeLevy P 𝓕, its literal marked jump count N_X((s,t]×B) factors in first moment against every event A measurable in its unchanged past 𝓕_s, provided a measurable functional F of the genuine shifted future increment path is proved equal to that literal count on every original sample. The conclusion contains no source-count intensity assumption, no Poisson-copy process and no new filtration. It is the conditional-expectation/sigma-algebra interface; source-path extractor measurability and the unconditional mark-specific ν(B) identity are explicit separate mathematical obligations.
-- source:
--   Proved original source future-path past-test kernel AvramDividend.Classical.avram_root29_01_original_future_kernel_past_test UUID 0611e261-f045-4fb5-a53c-a42f06995418, twice instantiated with past event A and Set.univ. Original-source same-path extractor transport b1721778 is Proved. W7-01 exact original intrinsic rectangle compensator 393b03a8 remains Open.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_original_future_kernel_past_test

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_01_intrinsic_future_rectangle_past_factor_of_measurable_extractor
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (B : Set ℝ) (hB : MeasurableSet B)
    (F : (ℝ≥0 → ℝ) → ℝ≥0∞) (hF : Measurable F)
    (hExtract : ∀ ω : Ω,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) =
      F (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω)) :
    (∫⁻ ω in A,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) =
    P A * (∫⁻ ω,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) := by sorry
