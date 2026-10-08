-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_adapted
-- name    : AvramDividend.Classical.barrierStrategy_adapted
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-05T10:07:04.940009+00:00
-- url     : https://prove2.me/theorems/80a2a8e7-8af9-4b39-a5d6-be993bc4aefc
-- title:
--   Barrier dividends are adapted to the Levy process filtration
-- statement:
--   The barrier dividend strategy at initial reserve equal to the barrier is adapted to the filtration of any spectrally negative Levy process. Choose a countable dense subset of nonnegative times containing zero; use right continuity to represent each time-supremum as a maximum of countably sampled past values and the current process value. Both terms are measurable with respect to the filtration at the current time.
-- source:
--   Conditional on the Prove2Me proofs of dense_timeSup_with_endpoint, countable_pastSup_adapted and barrierStrategy_adapted_of_countable_endpoint_representation. This is one of the required IsDividendStrategy laws for the Avram Dividend official value-function theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_one_sided_limits_bddAbove_Icc
import Theorems.Thm_AvramDividend_Classical_dense_timeSup_with_endpoint
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_adapted_of_countable_endpoint_representation

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.barrierStrategy_adapted {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (c : ℝ) :
    Adapted 𝓕 (barrierStrategy X c c) := by
  sorry
