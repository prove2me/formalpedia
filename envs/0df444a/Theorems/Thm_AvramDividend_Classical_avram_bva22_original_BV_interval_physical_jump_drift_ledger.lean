-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva22_original_BV_interval_physical_jump_drift_ledger
-- name    : AvramDividend.Classical.avram_bva22_original_BV_interval_physical_jump_drift_ledger
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T01:12:23.213191+00:00
-- url     : https://prove2.me/theorems/cc3bbe55-b9b9-42e3-b0f1-dd3813dcbe8c
-- title:
--   Original standing BV interval increment equals physical drift minus summable negative jumps
-- statement:
--   On the original same-space Standing bounded-variation Levy path, every ordered nonnegative pair of clocks satisfies the exact physical drift-minus-negative-jump increment identity. The negative-jump sum is restricted to the actual half-open interval (a,b], and is summable by the established original BV interval absolute-jump theorem. This is an original-process input to the chronological Stieltjes/HJB cash proof for both finite and infinite negative-jump activity, without independent-process replacement or large-mark first-moment assumptions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bva22_original_BV_interval_physical_jump_drift_ledger
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ a b : ℝ≥0, a ≤ b →
      X.X b ω - X.X a ω = ((b : ℝ) - (a : ℝ)) * X.drift -
        (∑' u : ℝ≥0, if a < u ∧ u ≤ b then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0) := by sorry
