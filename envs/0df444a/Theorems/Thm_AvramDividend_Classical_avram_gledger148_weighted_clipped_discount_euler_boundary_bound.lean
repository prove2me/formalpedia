-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger148_weighted_clipped_discount_euler_boundary_bound
-- name    : AvramDividend.Classical.avram_gledger148_weighted_clipped_discount_euler_boundary_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T20:09:20.670688+00:00
-- url     : https://prove2.me/theorems/89dc0f48-03ab-45e7-ac09-5b2c1e333071
-- title:
--   Weighted clipped crossing Euler remainder bounded linearly by mesh width
-- statement:
--   The genuine final clipped crossing mesh cell has discounted time Euler residual bounded in absolute value by twice q times the mesh width times a deterministic postpayment weight bound. This combines the clipped exponential crossing estimate with the clock drift counterterm, needed for original source gledger139.
-- source:
--   Proved gledger147 clipped discount bound, exponential discount factor at nonnegative time at most one, and absolute triangle and product inequalities.

import Mathlib
noncomputable section

theorem AvramDividend.Classical.avram_gledger148_weighted_clipped_discount_euler_boundary_bound
    (q t r δ a K : ℝ) (hq : 0 ≤ q) (ht : 0 ≤ t)
    (hr : 0 ≤ r) (hrδ : r ≤ δ) (hK : 0 ≤ K) (ha : |a| ≤ K) :
    |(Real.exp (-(q * (t + r))) - Real.exp (-(q * t)) +
        q * δ * Real.exp (-(q * t))) * a| ≤ 2 * q * δ * K := by sorry
