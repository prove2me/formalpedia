-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_original_zero_future_canonical_leftlim_cadlag
-- name    : AvramDividend.Classical.avram_p2_34dbea70_original_zero_future_canonical_leftlim_cadlag
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:23:47.547694+00:00
-- url     : https://prove2.me/theorems/92492a21-3f03-41d0-be24-23bef45df296
-- title:
--   Actual original zero-future Lévy path is right-continuous and tends to its canonical left limit
-- statement:
--   For every actual SpectrallyNegativeLevy source path on its original omega/probability/filtration, the zero-future increment path v ↦ X.X v omega - X.X 0 omega is right-continuous at all times and tends to its canonical Function.leftLim at every positive time from the strict left. This converts the Proved existential finite-left-limit source theorem into the exact regularity hypotheses required for the pathwise all-negative-jump liminf bridge; no replacement process or rate assumption is made.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_shifted_future_increment_path_cadlag

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_34dbea70_original_zero_future_canonical_leftlim_cadlag
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) :
    (∀ t : ℝ≥0, ContinuousWithinAt
      (fun v : ℝ≥0 => X.X v ω - X.X 0 ω) (Ici t) t) ∧
    (∀ u : ℝ≥0, 0 < u →
      Tendsto (fun v : ℝ≥0 => X.X v ω - X.X 0 ω)
        (𝓝[<] u)
        (𝓝 (Function.leftLim
          (fun v : ℝ≥0 => X.X v ω - X.X 0 ω) u))) := by sorry
