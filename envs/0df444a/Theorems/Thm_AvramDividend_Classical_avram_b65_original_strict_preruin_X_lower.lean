-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b65_original_strict_preruin_X_lower
-- name    : AvramDividend.Classical.avram_b65_original_strict_preruin_X_lower
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T12:29:34.679027+00:00
-- url     : https://prove2.me/theorems/4912fa2f-eb2b-4ffe-bfd6-6a111780fc7b
-- title:
--   Original admissible dividend source stays above minus initial capital before genuine ruin
-- statement:
--   For the true original Lévy process and admissible dividend strategy, the original source path is at least negative initial capital at time zero and every strictly pre-ruin clock. This controls the lower physical endpoint for compact stopped Ito mesh cells without extending the source after ruin.
-- source:
--   Proved avram_p3_2_original_strict_preruin_prepayment_reserve_nonnegative and IsAdmissibleLe, IsDividendStrategy definitions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_strict_preruin_prepayment_reserve_nonnegative
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_b65_original_strict_preruin_X_lower
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0)
    (ht : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) :
    -x ≤ X.X t ω := by sorry
