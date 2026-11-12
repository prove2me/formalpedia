-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger149_finite_clipped_discount_euler_total_weighted_bound
-- name    : AvramDividend.Classical.avram_gledger149_finite_clipped_discount_euler_total_weighted_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T20:14:17.11687+00:00
-- url     : https://prove2.me/theorems/febdb742-1b42-4cad-84b4-831d71d58be7
-- title:
--   Quadratic interior plus linear boundary discounted Euler finite-grid error
-- statement:
--   Aggregate the finite interior clipped source discount Taylor Euler cell errors and the single final clipped crossing cell, with a uniform compact postpayment weight bound. The entire deterministic physical-clock remainder is at most m times the quadratic local mesh error plus one linear boundary error. Applying the original mesh delta=n/(m+1) yields a vanishing rate for gledger139 once the original pathwise weights and masks are certified.
-- source:
--   Proved gledger146 interior sum absolute bound and gledger148 original clipped cell weighted bound via absolute triangle.

import Mathlib
noncomputable section

theorem AvramDividend.Classical.avram_gledger149_finite_clipped_discount_euler_total_weighted_bound
    (m : ℕ) (q δ K t r a : ℝ) (s weight : ℕ → ℝ)
    (hq : 0 ≤ q) (ht : 0 ≤ t) (hr : 0 ≤ r) (hrδ : r ≤ δ)
    (hK : 0 ≤ K) (ha : |a| ≤ K)
    (hw : ∀ i ∈ Finset.range m, |weight i| ≤ K)
    (hcell : ∀ i ∈ Finset.range m, |Real.exp (-(q * (s i + δ))) - Real.exp (-(q * s i)) + q * δ * Real.exp (-(q * s i))| ≤ (q * δ) ^ 2) :
    |Finset.sum (Finset.range m) (fun i => (Real.exp (-(q * (s i + δ))) - Real.exp (-(q * s i)) + q * δ * Real.exp (-(q * s i))) * weight i) +
      (Real.exp (-(q * (t + r))) - Real.exp (-(q * t)) + q * δ * Real.exp (-(q * t))) * a| ≤
      (m : ℝ) * ((q * δ) ^ 2 * K) + 2 * q * δ * K := by sorry
