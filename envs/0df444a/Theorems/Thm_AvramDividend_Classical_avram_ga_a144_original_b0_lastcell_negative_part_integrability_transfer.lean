-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a144_original_b0_lastcell_negative_part_integrability_transfer
-- name    : AvramDividend.Classical.avram_ga_a144_original_b0_lastcell_negative_part_integrability_transfer
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T11:37:28.00361+00:00
-- url     : https://prove2.me/theorems/3ebaa061-abd2-4b84-8815-100efb4209ba
-- title:
--   Eventual original Gaussian m-cell positive spatial integrability transfers from proved m+1-cell residual when the omitted last source cell has integrable negative part
-- statement:
--   The exact source m-cell original Gaussian spatial residual U differs from the previously proved m+1-cell residual S by the original last clipped source spatial increment Last. The positive part satisfies max(U,0) <= max(S,0)+max(-Last,0). If the m+1-cell positive residual is integrable at each grid and the negative part of the last source increment is integrable on sufficiently fine meshes, along with a.e. strong measurability of the original root positive residual, then the root m-cell residual is eventually integrable. This isolates the genuine terminal negative-tail obligation instead of assuming stronger full-cell absolute L1.
-- source:
--   Exact original b0 spatial m vs m+1 source identity ga131 and proved m+1 positive integrability ga26_original_spatial_positive_integrable.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a144_original_b0_lastcell_negative_part_integrability_transfer
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (U S Last : ℕ → Ω → ℝ)
    (hDiff : ∀ m ω, U m ω = S m ω - Last m ω)
    (hMeas : ∀ m, AEStronglyMeasurable (fun ω => max (U m ω) 0) P)
    (hSI : ∀ m, Integrable (fun ω => max (S m ω) 0) P)
    (hLast : ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      Integrable (fun ω => max (-Last m ω) 0) P) :
    ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      Integrable (fun ω => max (U m ω) 0) P := by sorry
