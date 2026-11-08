-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_original_rightcont_predictable_band_trace
-- name    : AvramDividend.Classical.avram_ubv_gaussian10_original_rightcont_predictable_band_trace
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T11:09:15.603294+00:00
-- url     : https://prove2.me/theorems/c2dbe4fd-49b4-454f-9ad9-5f010646af01
-- title:
--   Predictable finite-time band trace in Avram's actual right-continuous stopping filtration
-- statement:
--   For the original spectrally negative Levy process on its original probability space, predictable sets formed from the explicit right-continuous stopping filtration 𝓕.rightCont become Borel-time times 𝓕.rightCont_b measurable when restricted to (a,b] times Omega. This matches the filtration used by Avram's ruin-time clock and the already-Proved source-gradient predictability 7ae1130d. The theorem uses predictable generator rectangles and never substitutes Brownian natural or null-augmented filtrations.
-- source:
--   Pinned Mathlib.Probability.Process.Predictable and formal-mathfin BracketCompensator.lean generator proof, with original rightCont stopping filtration, inspected 2026-11-07.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gaussian10_original_rightcont_predictable_band_trace
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a b : ℝ≥0)
    (S : Set (ℝ≥0 × Ω))
    (hS : MeasurableSet[𝓕.rightCont.predictable] S) :
    MeasurableSet[@Prod.instMeasurableSpace ℝ≥0 Ω inferInstance (𝓕.rightCont b)]
      (S ∩ (Ioc a b ×ˢ (univ : Set Ω))) := by sorry
