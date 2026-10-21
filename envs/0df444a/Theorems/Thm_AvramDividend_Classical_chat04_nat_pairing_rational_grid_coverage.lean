-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_nat_pairing_rational_grid_coverage
-- name    : AvramDividend.Classical.chat04_nat_pairing_rational_grid_coverage
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T07:47:43.839978+00:00
-- url     : https://prove2.me/theorems/34d1a207-11c0-49d1-b331-c905323990f4
-- title:
--   Cantor-pairing observation schedule explicitly covers every nonnegative rational time
-- statement:
--   Use the exact revision's Cantor pairing map Nat.pair and its inverse Nat.unpair to construct an explicit countable enumeration of all grid times k/n for n>0 and k≥0. Define the j-th monitoring time as ((Nat.unpair j).2 : NNReal) divided by (((Nat.unpair j).1+1) : NNReal). For every n>0 and k, choose j=Nat.pair (n−1) k and prove the monitoring time equals k/n. The combinatorial construction supplies the concrete deterministic rational clock needed to apply the already compiled continuous strict survival characterisation and grid-expectation continuity theorem without an abstract enumeration-surjectivity premise.
-- source:
--   Pinned Mathlib.Data.Nat.Pairing Nat.unpair_pair, Nat.exists_eq_succ_of_ne_zero; NNReal casts. Subsequent use in the Chat04 continuous grid strict survival event theorem.

import Mathlib.Data.Nat.Pairing
import Mathlib.Data.NNReal.Basic

open scoped NNReal

theorem AvramDividend.Classical.chat04_nat_pairing_rational_grid_coverage
    (n k : ℕ) (hn : 0 < n) :
    ∃ j : ℕ,
      ((Nat.unpair j).2 : ℝ≥0) *
        ((((Nat.unpair j).1 + 1 : ℕ) : ℝ≥0)⁻¹) =
      (k : ℝ≥0) * (n : ℝ≥0)⁻¹ := by sorry
