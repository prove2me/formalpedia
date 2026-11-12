-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger146_finite_discount_Euler_cell_absolute_aggregation
-- name    : AvramDividend.Classical.avram_gledger146_finite_discount_Euler_cell_absolute_aggregation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T19:56:17.14619+00:00
-- url     : https://prove2.me/theorems/f89e0a0c-5293-4a14-8d83-655be375f532
-- title:
--   Finite uniform-mesh discount Euler absolute sum bound from one-cell estimates
-- statement:
--   If each interior discounted exponential Euler cell has quadratic error at most q squared delta squared and the original postpayment weight is bounded by K, the absolute aggregate error over m active interior cells is bounded by m times the cell bound times K. This is the deterministic finite-grid aggregation needed by the original gledger139 discount Euler L1 estimate.
-- source:
--   Real absolute finite-sum triangle inequality and termwise nonnegative multiplication. The one-cell bound is supplied by source-relevant exponential lemma gledger145 after enforcing q delta ≤ 1.

import Mathlib
noncomputable section

theorem AvramDividend.Classical.avram_gledger146_finite_discount_Euler_cell_absolute_aggregation
    (m : ℕ) (q δ K : ℝ) (s weight : ℕ → ℝ)
    (hK : 0 ≤ K)
    (hw : ∀ i ∈ Finset.range m, |weight i| ≤ K)
    (hcell : ∀ i ∈ Finset.range m,
      |Real.exp (-(q * (s i + δ))) - Real.exp (-(q * s i)) +
        q * δ * Real.exp (-(q * s i))| ≤ (q * δ) ^ 2) :
    |∑ i ∈ Finset.range m,
      (Real.exp (-(q * (s i + δ))) - Real.exp (-(q * s i)) +
        q * δ * Real.exp (-(q * s i))) * weight i| ≤
        (m : ℝ) * ((q * δ) ^ 2 * K) := by sorry
