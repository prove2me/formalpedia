-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a28_original_Borel_physical_window_count_factors_through_frozen_path_20261116
-- name    : AvramDividend.Classical.avram_a28_original_Borel_physical_window_count_factors_through_frozen_path_20261116
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T12:39:47.91997+00:00
-- url     : https://prove2.me/theorems/e133ceed-b5b1-4ea3-ae78-89ef4a5af87f
-- title:
--   Original physical Borel marked count on any half-open window factors measurably through the stopped original path
-- statement:
--   For any original spectrally negative Levy path, any s and T, and any measurable Borel jump set, the actual original physical marked jump count in (s,T] is a measurable functional of the original path frozen at T. Use the source-exact marked rectangle encard identity, agreement of the frozen and original jumps at positive times up to T, and the generic cadlag marked half-open window measurable functional. This preserves the original filtration and probability source.
-- source:
--   Proved source rectangle count encard f6336d40, frozen left-limit 8e873bf7, and generic half-open-window cadlag Borel count a28.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a28_original_Borel_physical_window_count_factors_through_frozen_path_20261116
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s T : ℝ≥0)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hCad : ∀ ω : Ω,
      (∀ u : ℝ≥0, ContinuousWithinAt
        (fun v : ℝ≥0 => X.X (min v T) ω) (Ici u) u) ∧
      (∀ u : ℝ≥0, 0 < u →
        ∃ l : ℝ, Tendsto (fun v : ℝ≥0 => X.X (min v T) ω)
          (𝓝[<] u) (𝓝 l))) :
    ∃ F : (ℝ≥0 → ℝ) → ℝ≥0∞,
      Measurable F ∧ ∀ ω : Ω,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s T ×ˢ B) =
        F (fun v : ℝ≥0 => X.X (min v T) ω) := by sorry
