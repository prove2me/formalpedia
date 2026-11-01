-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_intrinsic_grid_count_eq_source_jump_count_ae_short_partition
-- name    : AvramDividend.Classical.avram_wave4_04a_bv_actual_intrinsic_grid_count_eq_source_jump_count_ae_short_partition
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T22:16:31.26245+00:00
-- url     : https://prove2.me/theorems/7df2397f-dc8a-4263-a8ea-c3e656b0de16
-- title:
--   Actual finite-activity BV Lévy intrinsic jump count equals fine strictly monotone partition occupancy on one full original-path event
-- statement:
--   For the genuine original-source BV finite-activity spectrally negative Lévy path, a single P-full event provides δ(ω,T)>0 so that for every finite strictly increasing partition grid from time zero to horizon T with all adjacent cell metric widths below δ, the literal intrinsic original-X jump counting measure N_X((0,T]×ℝ) equals the number of grid cells occupied by a nonzero actual X jump. Only geometric finiteness and source path separation are used; the theorem does not yet identify the grid occupancy law with a Poisson distribution, nor establish compensation.
-- source:
--   Canonically Proved source jump-time finite horizon 6a65718c-c002-4f92-98e7-85d17ced83e5; source short-cell one-per-jump interface when canonically Proved; source exact intrinsic N_X grid cardinal bijection 2ed18d64-48df-4745-a906-7177cbdab24c. Derive cover of (0,T] by all strictly increasing right-closed cells using Nat.find on smallest endpoint exceeding u, and unique index by monotonicity. Import original source-X and retain original Ω,P,ω,𝓕. No constructed equal-law process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_04a_bv_actual_intrinsic_grid_count_eq_source_jump_count_ae_short_partition
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ ω ∂P, ∃ δ : ℝ, 0 < δ ∧
      ∀ (n : ℕ) (grid : ℕ → ℝ≥0),
        StrictMono grid → grid 0 = 0 → grid n = T →
        (∀ i : ℕ, i < n →
          dist (grid i) (grid (i + 1)) < δ) →
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω - Function.leftLim
            (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 T ×ˢ (Set.univ : Set ℝ)) =
        ({i : ℕ | i < n ∧ ∃ u : ℝ≥0,
          u ≤ T ∧ 0 < u ∧
          X.X u ω - Function.leftLim
            (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
          u ∈ Ioc (grid i) (grid (i + 1))}.ncard : ENNReal) := by sorry
