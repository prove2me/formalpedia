-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_coordinatewise_weighted_R_mesh_L1
-- name    : AvramDividend.Classical.avram_bv_residual10_original_coordinatewise_weighted_R_mesh_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T12:22:23.343201+00:00
-- url     : https://prove2.me/theorems/e73d8d37-9447-48a1-8417-0e9ff69f072b
-- title:
--   Coordinatewise measurable bounded original Levy residual mesh is L1
-- statement:
--   For the literal original bounded-variation spectrally negative Levy process and deterministic mesh starting at zero and ending by T, any path-dependent real grid coefficients that are uniformly bounded and individually a.e. strongly measurable yield an integrable weighted original raw-residual mesh. Original finite-time residual L1 and coordinatewise measurability are derived from the standing assumptions and existing Proved source theorems. The overall finite sum measurability follows from its finite measurable summands. This directly discharges a formerly explicit whole-grid measurability assumption of c110a1c4 without changing the original filtration, stopping or jumps.
-- source:
--   AVRAM BV-RESIDUAL10 coordinatewise-measurable original raw R finite-grid L1, 7 November 2026

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a19_nonint_original_raw_R_coordinate_measurable
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_raw_R_fixed_time_L1
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_bounded_weighted_R_mesh_L1

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_residual10_original_coordinatewise_weighted_R_mesh_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (T : ℝ≥0) (u : ℕ → ℕ → ℝ≥0) (n : ℕ)
    (hu : ∀ i, i < n + 1 → u n i ≤ u n (i + 1))
    (hu0 : u n 0 = 0) (huT : u n (n + 1) ≤ T)
    (a : Ω → ℕ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hBound : ∀ ω, ∀ i ∈ Finset.range (n + 1), |a ω i| ≤ K)
    (hMeasA : ∀ i, AEStronglyMeasurable (fun ω => a ω i) P) :
    Integrable (fun ω =>
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) -
          (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
          else 0)
      ∑ i ∈ Finset.range (n + 1),
        a ω i * (R (u n i) - R (u n (i + 1)))) P := by sorry
