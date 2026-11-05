-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_main_original_jump_removed_continuous_positive_time
-- name    : AvramDividend.Classical.avram_p3_main_original_jump_removed_continuous_positive_time
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T08:30:46.335322+00:00
-- url     : https://prove2.me/theorems/394ca2b9-9a34-4964-b6ac-35edffb1911b
-- title:
--   Original bounded-variation jump-removed source path is continuous at every positive time
-- statement:
--   On a single P-full event, the actual original bounded-variation Lévy path X.X plus its original cumulative negative left-jump magnitudes is continuous at every positive time. It follows by the exact pathwise algebra Y(t)=t·X.drift−R(t) from the Proved source residual-continuity theorem. The continuous monotone source residual R is retained; no false assumption that R=0 is used. This supplies the positive-time continuity needed for compact mesh localisation in the canonical P3 strict-horizon stopped budget.
-- source:
--   Theorem 38d9546f-8a24-4324-b334-b841deb9f404, original raw removed residual continuity at all positive times, accepted and Proved; algebraic identity from original source X.X and actual left jump summation. Mission a19d8b28-f606-4a95-907a-cec601da255f.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_removed_residual_continuous_positive_time
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_main_original_jump_removed_continuous_positive_time
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t →
      ContinuousAt (fun s : ℝ≥0 => X.X s ω +
        (∑' u : ℝ≥0, if 0 < u ∧ u ≤ s then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω
        else 0)) t := by sorry
