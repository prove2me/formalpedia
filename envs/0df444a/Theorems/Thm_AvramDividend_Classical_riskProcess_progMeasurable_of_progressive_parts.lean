-- Prove2me | Theorems.Thm_AvramDividend_Classical_riskProcess_progMeasurable_of_progressive_parts
-- name    : AvramDividend.Classical.riskProcess_progMeasurable_of_progressive_parts
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T10:33:20.797568+00:00
-- url     : https://prove2.me/theorems/f27f93ec-fa99-4721-8b5d-33eb31d4a90f
-- title:
--   Progressive Lévy and dividend components give progressively measurable controlled reserve
-- statement:
--   The affine controlled risk process inherits progressive measurability from the underlying spectrally negative Lévy path and admissible dividend path, without requiring sample-path continuity. This isolates the purely algebraic combination step from the unresolved progressive-measurability proofs for càdlàg X and càglàd D.
-- source:
--   MeasureTheory.IsStronglyProgressive.add/sub and isStronglyProgressive_const in pinned Mathlib. The fixed decomposition riskProcess = x + X.X - D.

import Mathlib.Probability.Process.Adapted
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.riskProcess_progMeasurable_of_progressive_parts
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hXProg : ProgMeasurable 𝓕 X.X)
    (hDProg : ProgMeasurable 𝓕 D) :
    ProgMeasurable 𝓕 (riskProcess X x D) := by sorry
