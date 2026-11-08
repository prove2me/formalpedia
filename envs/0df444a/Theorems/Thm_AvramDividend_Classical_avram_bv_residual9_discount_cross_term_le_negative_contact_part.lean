-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_residual9_discount_cross_term_le_negative_contact_part
-- name    : AvramDividend.Classical.avram_bv_residual9_discount_cross_term_le_negative_contact_part
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T12:24:23.379202+00:00
-- url     : https://prove2.me/theorems/02f60d09-29df-4836-b220-265bfb6c83b1
-- title:
--   Stopped BV discount commutator has positive contribution only from negative post-cell values
-- statement:
--   For a nondecreasing original physical grid and nonnegative discount rate, the sum of discounted endpoint-value commutators is bounded above by the corresponding nonnegative discount weights multiplied by the negative parts of the next postpayment cell values. This isolates the only potentially positive ruin/horizon contact contribution without asserting that its expected value vanishes.
-- source:
--   AVRAM BV-RESIDUAL9 round-four discounted six-term original-cell analysis

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_residual9_discount_cross_term_le_negative_contact_part
    (q : ℝ) (hq : 0 ≤ q)
    (u : ℕ → ℝ≥0) (m : ℕ)
    (hmono : ∀ i, i < m + 1 → u i ≤ u (i + 1))
    (post : ℕ → ℝ) :
    (∑ i ∈ Finset.range (m + 1),
      (Real.exp (-(q * (u (i + 1) : ℝ))) -
        Real.exp (-(q * (u i : ℝ)))) * post (i + 1)) ≤
      (∑ i ∈ Finset.range (m + 1),
        (Real.exp (-(q * (u i : ℝ))) -
          Real.exp (-(q * (u (i + 1) : ℝ)))) * max (-post (i + 1)) 0) := by sorry
