-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_bv_cofinal_weighted_spatial_error_diagonal
-- name    : AvramDividend.Classical.avram_a06_bv_cofinal_weighted_spatial_error_diagonal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T14:16:20.340196+00:00
-- url     : https://prove2.me/theorems/16975517-1ad5-4723-9bd5-b1e6857e3944
-- title:
--   A06 BV cofinal spatial localisation with arbitrarily growing nonnegative row weight
-- statement:
--   Every nonnegative spatial tail error with mean converging to zero along spatial compact-band exhaustion at each fixed physical time-grid row admits a strictly increasing cofinal spatial-band selection such that the error multiplied by an arbitrary nonnegative row-dependent localisation constant still converges to zero. This diagonal result controls growing local C1 Lipschitz/derivative constants in original BV stopped mesh localisation. It is a direct corollary of the Proved monotone diagonal theorem, without signed HJB integrability assumptions.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bv_strict6_monotone_diagonal_mean
open MeasureTheory Set Filter AvramDividend.Classical
open scoped Topology
noncomputable section

theorem AvramDividend.Classical.avram_a06_bv_cofinal_weighted_spatial_error_diagonal
    (E : ℕ → ℕ → ℝ)
    (hE : ∀ n k, 0 ≤ E n k)
    (hTail : ∀ n, Tendsto (fun k => E n k) atTop (𝓝 (0 : ℝ)))
    (L : ℕ → ℝ) (hL : ∀ n, 0 ≤ L n) :
    ∃ κ : ℕ → ℕ, StrictMono κ ∧ (∀ n, n ≤ κ n) ∧
      Tendsto (fun n => (1 + L n) * E n (κ n))
        atTop (𝓝 (0 : ℝ)) := by sorry
