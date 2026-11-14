-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB298_original_bad_grid_hit_event_joint_measurable
-- name    : AvramDividend.Classical.avram_gbB298_original_bad_grid_hit_event_joint_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T23:25:32.734413+00:00
-- url     : https://prove2.me/theorems/b214b3cb-c464-48a3-b381-32c6b1b34a61
-- title:
--   Localised original dividend bad-grid prescribed-level hit event is jointly measurable
-- statement:
--   For any original spectrally negative Levy source and truly adapted dividend strategy, the outcome-by-physical-time event of a fixed reserve level hit inside one of finitely many bad dividend-increment cells, under a terminal dividend-variation localisation, is jointly measurable. Original reserve joint measurability follows from Proved B269, and dividend payment sections from adaptedness; finite intersections and unions preserve measurability. This enables the source-specific B290 bad-cell Tonelli estimate in the B276b occupation proof.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory ProbabilityTheory AvramDividend.Classical Set Finset
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB298_original_bad_grid_hit_event_joint_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x b : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (n m M : ℕ) :
    MeasurableSet {z : Ω × ℝ | ∃ i ∈ Finset.range (n * m ^ 4),
      z.2 ∈ Set.Ioo
        ((i : ℝ) * (1 / ((m : ℝ) ^ 4)))
        (((i : ℝ) + 1) * (1 / ((m : ℝ) ^ 4))) ∧
      1 / ((m : ℝ) ^ 3) <
        D (((i + 1 : ℕ) : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) z.1 -
        D ((i : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) z.1 ∧
      x + X.X (Real.toNNReal z.2) z.1 -
        rightLimit D (Real.toNNReal z.2) z.1 = b ∧
      D n z.1 - D 0 z.1 ≤ (M : ℝ)} := by sorry
