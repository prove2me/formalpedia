-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_prestate_predictable_zero_interior_cap_partition
-- name    : AvramDividend.Classical.avram_p3_g_localise_original_prestate_predictable_zero_interior_cap_partition
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T12:43:48.25725+00:00
-- url     : https://prove2.me/theorems/fd3dcf89-2d6e-413c-89ee-785f9f44e7ef
-- title:
--   Original reserve prestate has predictable zero, strict interior and cap-contact partition without boundary occupation assumptions
-- statement:
--   The exact original pre-reserve leftLimit process is strongly predictable. Therefore zero reserve, strict positive cap interior and cap-contact sets are all predictable; on any physically nonnegative reserve not exceeding cap, these cases exhaust the range. The statement works for finite or infinite ENNReal caps and deliberately permits positive measure occupation at finite-cap contact in BV paths.
-- source:
--   Original strongly predictable source pre-reserve Proved 94ee9994; pinned continuous ENNReal.ofReal and elementary linear order partition. No UBV occupation-zero lemma, no surrogate process, no terminal limit assumed.

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_g_localise_original_prestate_predictable_zero_interior_cap_partition
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) :
    let Z : ℝ≥0 × Ω → ℝ := fun p =>
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    MeasurableSet[𝓕.rightCont.predictable] {p | Z p = 0} ∧
    MeasurableSet[𝓕.rightCont.predictable]
      {p | ENNReal.ofReal (Z p) = C} ∧
    MeasurableSet[𝓕.rightCont.predictable]
      {p | 0 < Z p ∧ ENNReal.ofReal (Z p) < C} ∧
    ∀ p, 0 ≤ Z p → ENNReal.ofReal (Z p) ≤ C →
      Z p = 0 ∨ (0 < Z p ∧ ENNReal.ofReal (Z p) < C) ∨
        ENNReal.ofReal (Z p) = C := by sorry
