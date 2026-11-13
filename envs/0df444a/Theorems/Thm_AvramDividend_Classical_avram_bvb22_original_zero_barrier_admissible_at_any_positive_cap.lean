-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb22_original_zero_barrier_admissible_at_any_positive_cap
-- name    : AvramDividend.Classical.avram_bvb22_original_zero_barrier_admissible_at_any_positive_cap
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T00:06:09.207686+00:00
-- url     : https://prove2.me/theorems/cd8f52c6-db8d-4b9b-8d4f-915d342ebd23
-- title:
--   Original zero barrier dividend strategy is admissible at every strictly positive dividend reserve cap
-- statement:
--   The original zero-barrier strategy at zero initial reserve is source-admissible at cap zero by a Proved theorem. Because IsAdmissibleLe preserves the original admissibility conditions and only relaxes the reserve cap, the same original barrier strategy is admissible at every strictly positive finite cap. This resolves the all-omega admissibility issue in the original finite-activity physical zero-contact counterexample candidate while retaining the actual right-limit dividend definition.
-- source:
--   Proved original barrierStrategy_admissibleLe_nonnegative_barrier 32b4ccb8, original DividendStrategy definition.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_admissibleLe_nonnegative_barrier
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bvb22_original_zero_barrier_admissible_at_any_positive_cap
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : ℝ≥0∞) (hC : 0 < C) :
    IsAdmissibleLe X 0 C (barrierStrategy X 0 0) := by sorry
