-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger121_first_crossing_cash_contact_finite_algebra
-- name    : AvramDividend.Classical.avram_gledger121_first_crossing_cash_contact_finite_algebra
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T14:44:02.412046+00:00
-- url     : https://prove2.me/theorems/1d5e93e8-d6cc-4c53-a216-3960617907f4
-- title:
--   Original stopped cash and contact finite algebra at first crossing
-- statement:
--   If all original contact cells after the exact crossing are zero, complete-cell contact plus cash is bounded by a mesh source, the crossing contact and terminal and initial contact cancel their corresponding cash, and the strict cash decomposes into those pieces, the positive part of the full original stopped ledger is bounded by the mesh source and last strip.
-- source:
--   Finite algebraic final step assembling original original-process gledger81 stopped dividend-contact correction.

import Mathlib
open Finset
noncomputable section

theorem AvramDividend.Classical.avram_gledger121_first_crossing_cash_contact_finite_algebra
    (A : ℕ → ℝ) (N k : ℕ) (hk : k < N)
    (hafter : ∀ i : ℕ, k < i → A i = 0)
    (I U R F z cash0 term : ℝ)
    (hpre : (∑ i ∈ Finset.range k, A i) + I ≤ R)
    (hlast : A k + term ≤ 0)
    (hzero : z + cash0 ≤ 0)
    (hcash : F ≤ cash0 + I + U)
    (herr : 0 ≤ R + U) :
    max (z + (∑ i ∈ Finset.range N, A i) + term + F) 0 ≤ R + U := by sorry
