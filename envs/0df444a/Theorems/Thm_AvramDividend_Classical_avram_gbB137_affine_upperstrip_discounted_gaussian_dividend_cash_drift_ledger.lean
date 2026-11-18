-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB137_affine_upperstrip_discounted_gaussian_dividend_cash_drift_ledger
-- name    : AvramDividend.Classical.avram_gbB137_affine_upperstrip_discounted_gaussian_dividend_cash_drift_ledger
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T18:49:55.90687+00:00
-- url     : https://prove2.me/theorems/b930e4c9-c735-4d14-8d7d-ee8021d6bc46
-- title:
--   Affine caplinear upper-strip Gaussian dividend cash retains the exact positive drift term
-- statement:
--   Specialise the Proved original finite discounted Gaussian dividend-cash Abel ledger B57 to the upper caplinear reward V(y)=y+κ. The exact cash minus centred Brownian noise equals 2 times the discounted physical time increments, minus discount-weight differences against the reflected reserve, plus the terminal-minus-initial affine intercept correction (a_m−a_0)κ. This exposes the positive drift contribution that cannot be ignored in the original fixed-band caplinear cash bound.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB57_original_gaussian_finite_discounted_cash_abel_ledger
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_gbB137_affine_upperstrip_discounted_gaussian_dividend_cash_drift_ledger
    (m : ℕ) (a B s D : ℕ → ℝ) (C κ : ℝ) :
    let Y : ℕ → ℝ := fun i => C + B i + 2 * s i - D i
    a m * (Y (m + 1) + κ) +
      (Finset.range (m + 1)).sum (fun i => a i * (D (i + 1) - D i)) -
      a 0 * (Y 0 + κ) -
      (Finset.range (m + 1)).sum (fun i => a i * (B (i + 1) - B i)) =
    2 * (Finset.range (m + 1)).sum (fun i => a i * (s (i + 1) - s i)) -
      (Finset.range m).sum (fun i => (a i - a (i + 1)) * Y (i + 1)) +
      (a m - a 0) * κ := by sorry
