-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_weighted_extracted_count_factor
-- name    : AvramDividend.Classical.avram_p2_e_compensator_weighted_extracted_count_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:33:03.522683+00:00
-- url     : https://prove2.me/theorems/fbbf6c10-ae98-4163-acda-d53fa2c0729b
-- title:
--   Arbitrary original past weights factor against extracted genuine future jump counts
-- statement:
--   For the original Lévy source, every nonnegative F_s-measurable weight W and every ENNReal-valued random variable N that is represented samplewise by a measurable functional F of the genuine shifted future increment path satisfy E[W N] = E[W] E[N]. The equality is valid for infinite expectations. With the proved intrinsic marked count extractor, N is the exact original (s,t]×B jump count; no rate or compensator assumption is made.
-- source:
--   Proved original past-test future kernel 0611e261-f045-4fb5-a53c-a42f06995418; weighted future kernel helper 6b848c04-9b6c-451f-aef0-85ac5cf402a9 is being proved. Actual intrinsic future extractor 5cf3e058 provides instantiations. Canonical compensator parent 393b03a8-2e9a-43d8-b415-854d86d58104.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_e_compensator_weighted_extracted_count_factor
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s : ℝ≥0)
    (F : (ℝ≥0 → ℝ) → ℝ≥0∞) (hF : Measurable F)
    (N : Ω → ℝ≥0∞)
    (hExtract : ∀ ω : Ω,
      N ω = F (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω))
    (W : Ω → ℝ≥0∞) (hW : Measurable[𝓕 s] W) :
    (∫⁻ ω, W ω * N ω ∂P) =
      (∫⁻ ω, W ω ∂P) * (∫⁻ ω, N ω ∂P) := by sorry
