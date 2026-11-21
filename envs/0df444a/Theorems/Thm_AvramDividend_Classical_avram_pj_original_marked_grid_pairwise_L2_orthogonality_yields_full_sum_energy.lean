-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_original_marked_grid_pairwise_L2_orthogonality_yields_full_sum_energy
-- name    : AvramDividend.Classical.avram_pj_original_marked_grid_pairwise_L2_orthogonality_yields_full_sum_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T09:46:09.018185+00:00
-- url     : https://prove2.me/theorems/85fd3863-73bf-46c2-afb2-d4b848350a1c
-- title:
--   Distinct-cell compensated marked martingale orthogonality upgrades diagonal grid energy to the full squared stopped sum
-- statement:
--   For any genuine probability or general measure, integrable products of all original stopped physical-grid cell martingale increments and zero covariance of every distinct pair imply exact equality of the second moment of the complete compensated martingale sum and the sum of diagonal energies. This isolates the genuine stochastic cross-cell orthogonality obligation needed to turn the original proved diagonal negative-mark isometry into a uniform full-sum L2 bound.

import Mathlib
open MeasureTheory Set
noncomputable section

theorem AvramDividend.Classical.avram_pj_original_marked_grid_pairwise_L2_orthogonality_yields_full_sum_energy
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (s : Finset ℕ) (Z : ℕ → Ω → ℝ)
    (hPair : ∀ i ∈ s, ∀ j ∈ s,
      Integrable (fun ω => Z i ω * Z j ω) P)
    (hCross : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      (∫ ω, Z i ω * Z j ω ∂P) = 0) :
    (∫ ω, (∑ i ∈ s, Z i ω)^2 ∂P) =
      ∑ i ∈ s, ∫ ω, (Z i ω)^2 ∂P := by sorry
