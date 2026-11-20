-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a19_finitecap_raw_w_overshoot_identity
-- name    : AvramDividend.Classical.avram_a19_finitecap_raw_w_overshoot_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T23:03:11.644014+00:00
-- url     : https://prove2.me/theorems/5627158e-e38f-4da4-a108-c4622aa8ab77
-- title:
--   Exact above-cap raw dividend cell overshoot penalty
-- statement:
--   For a cap-one HJB candidate w(y)=y at and below the cap, and w(y)=1-sqrt(y-1) above the cap, the original grid dividend residual in a cell with nonnegative dividend increment d and postpayment cap shortfall r in [0,1] equals the positive overshoot max(d-r,0) plus its square root. This is an algebraic certificate of the uncontrolled prepayment state w(Z) risk in original finite-cap physical grids. It does not assert a full Lévy sample-path counterexample.
-- source:
--   Exact deterministic algebra for raw finite-cap prepayment HJB cell, motivated by 0fc16aa4, 2f5776f6 and c4859e0e; separate from stochastic counterexample.

import Mathlib

theorem AvramDividend.Classical.avram_a19_finitecap_raw_w_overshoot_identity
    (d r : ℝ) (hd : 0 ≤ d) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    let w : ℝ → ℝ := fun z =>
      if z ≤ 1 then z else 1 - Real.sqrt (z - 1)
    d + w (1 - r) - w (1 - r + d)
      = max (d - r) 0 + Real.sqrt (max (d - r) 0) := by sorry
