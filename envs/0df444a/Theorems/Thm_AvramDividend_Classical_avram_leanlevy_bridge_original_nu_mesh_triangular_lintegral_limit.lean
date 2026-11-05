-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_leanlevy_bridge_original_nu_mesh_triangular_lintegral_limit
-- name    : AvramDividend.Classical.avram_leanlevy_bridge_original_nu_mesh_triangular_lintegral_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:16:21.805942+00:00
-- url     : https://prove2.me/theorems/ee7d7d7b-0779-4d3d-86ad-abe1ca06d43b
-- title:
--   Original Lévy negative-band quadratic grid rate converges in ENNReal
-- statement:
--   For the genuine spectrally negative Lévy process X on the original probability space and its actual negative-band intensity (X.ν B).toReal, the physical equal-mesh factorial-rate expression, lifted to ENNReal, converges to the lifted half-square rate. This supplies the exact real-to-ENNReal topology adapter for the original P2-E and P4-F pair-moment programme; conversion of original finite-grid expectations to this deterministic expression remains a separate source obligation.
-- source:
--   Accepted original triangular rate limit 5c5897cb-27d0-4352-b06b-d3d64b8202b0 and pinned Mathlib ENNReal.continuous_ofReal, verified in the pinned declaration index.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_leanlevy_bridge_original_equal_mesh_triangular_limit_real
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_leanlevy_bridge_original_nu_mesh_triangular_lintegral_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ) :
    let a : ℝ := (X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
    Tendsto
      (fun m : ℕ => ENNReal.ofReal
        (((m : ℝ) * ((m : ℝ) - 1) / 2) *
          (((T : ℝ) * a) ^ 2 / (m : ℝ) ^ 2)))
      atTop (𝓝 (ENNReal.ofReal (((T : ℝ) * a) ^ 2 / 2))) := by sorry
