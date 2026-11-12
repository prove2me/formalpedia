-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja35_original_negative_borel_real_count_first_moment
-- name    : AvramDividend.Classical.avram_ja35_original_negative_borel_real_count_first_moment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T22:32:56.857783+00:00
-- url     : https://prove2.me/theorems/4faa7c77-528b-433d-84b2-bdad7582ed6d
-- title:
--   Original finite-activity negative Borel count is real-integrable with exact mean T ν(B)
-- statement:
--   Convert the fully proved physical ENNReal Campbell first moment for arbitrary negative Borel jump-mark sets into finite integrable real count with the matching real expectation. Finiteness follows from finite negative jump intensity and is needed by exact factorial-to-variance algebra for the JA32 source theorem.
-- source:
--   Proved original arbitrary Borel Campbell first moment ja34 0d444e07 and original Borel rectangle count measurability 8146a449; pinned Mathlib integral_toReal/integrable_toReal_of_lintegral_ne_top.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja35_original_negative_borel_real_count_first_moment
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B)
    (hNeg : B ⊆ Iio (0 : ℝ)) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)
    Integrable (fun ω => (N ω).toReal) P ∧
      (∫ ω, (N ω).toReal ∂P) =
        ((T : ℝ≥0∞) * X.ν B).toReal := by sorry
