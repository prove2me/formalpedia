-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_removed_residual_right_continuous
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_original_raw_removed_residual_right_continuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T16:12:34.649529+00:00
-- url     : https://prove2.me/theorems/ae93cdd6-06ce-49ba-800a-6ecf58272ee7
-- title:
--   Original BV source physical-drift residual after actual raw jump removal is right-continuous
-- statement:
--   For the original spectrally negative bounded-variation Levy source, after subtracting its actual raw left-jump cumulative series, the physical drift residual is right-continuous for P-almost every original path and every time including zero. No Poisson replacement or assumed representation is involved.
-- source:
--   Source SpectrallyNegativeLevy.rightCont, original BV signed jump summability, and P3-A right atomic series convergence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_jump_cumulative_right_continuous

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The genuine original BV source drift residual after removing
its negative left-jump sum is right-continuous for every sample path. -/

theorem AvramDividend.Classical.avram_p3_a_bvdrift_original_raw_removed_residual_right_continuous
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Filter.Tendsto (fun s : ℝ≥0 =>
        (((s : ℝ) * X.drift - X.X s ω) -
          (∑' u : ℝ≥0, if 0 < u ∧ u ≤ s then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0)))
        (𝓝[>] t)
        (nhds ((((t : ℝ) * X.drift - X.X t ω) -
          (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0)))) := by sorry
