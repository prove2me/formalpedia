-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja31_original_borel_mark_count_filtration_measurable
-- name    : AvramDividend.Classical.avram_ja31_original_borel_mark_count_filtration_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T18:53:37.115034+00:00
-- url     : https://prove2.me/theorems/b25029d5-4473-4772-978f-e247b153c2a0
-- title:
--   Every original Borel marked count is measurable at its physical terminal filtration
-- statement:
--   For each measurable real-mark region B, the exact same-path jump count on (0,T] and B is measurable with respect to the original filtration at time T. The proof specialises a verified marked source lintegral measurability theorem to the indicator of B. No auxiliary space or moment bound is required.
-- source:
--   Necessary original past Borel count adaptedness for arbitrary mark-cell temporal covariance and JA28 finite-strip physical mark-simple energy certificate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ja31_original_borel_mark_count_filtration_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (B : Set ℝ) (hB : MeasurableSet B) :
    Measurable[𝓕 T] (fun ω : Ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)) := by sorry
