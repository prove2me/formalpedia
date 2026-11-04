-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_removed_residual_continuous_all_time
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_original_raw_removed_residual_continuous_all_time
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:29:48.890232+00:00
-- url     : https://prove2.me/theorems/56ed0b8e-04ab-40f9-ac91-f7e5cabdf46b
-- title:
--   Genuine original bounded-variation Lévy residual is continuous at every nonnegative time
-- statement:
--   On a single P-full event, the original bounded-variation spectrally negative Levy source path minus its genuine raw negative jump tsum and physical drift is continuous at all times including zero. The positive-time bridge is already proved; the zero endpoint follows from right convergence and the nonnegative-time neighborhood decomposition.
-- source:
--   Previously Proved original raw residual positive-time continuity and right-limit identity, plus pinned order-topological neighborhood decomposition on ℝ≥0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_removed_residual_continuous_positive_time
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_removed_residual_right_continuous

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p3_a_bvdrift_original_raw_removed_residual_continuous_all_time
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, Continuous (fun t : ℝ≥0 =>
      (((t : ℝ) * X.drift - X.X t ω) -
        (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0))) := by sorry
