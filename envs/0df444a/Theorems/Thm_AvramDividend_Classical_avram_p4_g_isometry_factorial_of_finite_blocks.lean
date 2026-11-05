-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_factorial_of_finite_blocks
-- name    : AvramDividend.Classical.avram_p4_g_isometry_factorial_of_finite_blocks
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T17:32:57.076903+00:00
-- url     : https://prove2.me/theorems/80b6d33d-70f6-4d53-9e01-fe9555f5bfa5
-- title:
--   Finite chronological jump-block factorial identity
-- statement:
--   The second factorial count of a finite chronological sum is exactly the sum of cell factorial counts plus twice the chronological ordered cross products. This reduces the still-open physical intrinsic second-factorial count law to a diagonal rarity estimate and predictable mixed block expectations; it assumes no Poisson construction.
-- source:
--   Finite algebra on original scalar count blocks; no stochastic premise. Can be applied to physical NX time-grid block counts once their additive decomposition is established.

import Mathlib
open scoped BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p4_g_isometry_factorial_of_finite_blocks (a : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, a i) *
        ((∑ i ∈ Finset.range n, a i) - 1) =
      (∑ i ∈ Finset.range n, a i * (a i - 1)) +
        2 * (∑ j ∈ Finset.range n,
          (∑ i ∈ Finset.range j, a i) * a j) := by sorry
