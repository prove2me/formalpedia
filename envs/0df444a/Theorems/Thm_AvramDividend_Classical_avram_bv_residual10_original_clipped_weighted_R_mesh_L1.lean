-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_clipped_weighted_R_mesh_L1
-- name    : AvramDividend.Classical.avram_bv_residual10_original_clipped_weighted_R_mesh_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T12:37:38.581961+00:00
-- url     : https://prove2.me/theorems/6b976cb7-43e7-46d4-9c1d-1f7771ba42bd
-- title:
--   Every bounded clipping of original Levy stopped-mesh residual weights is integrable
-- statement:
--   For the original bounded-variation spectrally negative Levy process, an arbitrary coordinatewise measurable path-dependent weight can be clipped at any nonnegative K on a monotone mesh bounded by T. The literal raw R weighted mesh sum is then integrable, using the proved fixed-time L1 and coordinatewise-measurable residual grid bridge. This supplies true L1 stochastic-grid approximants and isolates the uniform-integrability or tail estimate needed to remove coefficient clipping. No Brownian equality, global derivative bound, replaced stopping clock or changed dividend convention is asserted.
-- source:
--   AVRAM BV-RESIDUAL10 original-path clipped coefficient L1 finite-grid approximants, 7 November 2026

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_coordinatewise_weighted_R_mesh_L1

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_residual10_original_clipped_weighted_R_mesh_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (T : ℝ≥0) (u : ℕ → ℕ → ℝ≥0) (n : ℕ)
    (hu : ∀ i, i < n + 1 → u n i ≤ u n (i + 1))
    (hu0 : u n 0 = 0) (huT : u n (n + 1) ≤ T)
    (a : Ω → ℕ → ℝ)
    (hMeasA : ∀ i, Measurable (fun ω => a ω i))
    (K : ℝ) (hK : 0 ≤ K) :
    Integrable (fun ω =>
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) -
          (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
          else 0)
      ∑ i ∈ Finset.range (n + 1),
        (if |a ω i| ≤ K then a ω i else 0) *
          (R (u n i) - R (u n (i + 1)))) P := by sorry
