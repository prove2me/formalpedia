-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger164_finite_clipped_discount_weighted_euler_rate
-- name    : AvramDividend.Classical.avram_gledger164_finite_clipped_discount_weighted_euler_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T21:30:46.885082+00:00
-- url     : https://prove2.me/theorems/f1abf94f-0ada-438e-97a8-cf55db7b9522
-- title:
--   Exact finite stopped-grid weighted discount Euler error with one terminal crossing
-- statement:
--   Fully deterministic finite clipped uniform partition. For the exact grid n/(m+1) stopped at 0≤rho≤n, with only active physical cell weights bounded by K, the sum of all clipped exponential differences and active Riemann discount terms is bounded by m quadratic interior errors plus a single linear crossing error. Includes rho=0 and the last cell m without a Riemann term. Eliminates stochastic names while preserving exact source finite sums. Needed by gledger161 original pathwise Euler rate, together with original compact weight bound gledger162.
-- source:
--   Proved gledger149 finite weighted cell bound and gledger163 unique crossing, exact stopped uniform n/(m+1) and explicit absent terminal right sum.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gledger149_finite_clipped_discount_euler_total_weighted_bound
import Theorems.Thm_AvramDividend_Classical_avram_gledger163_true_uniform_clipped_mesh_first_crossing
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger164_finite_clipped_discount_weighted_euler_rate
    (n m : ℕ) (hn : 0 < n) (ρ : ℝ≥0) (hρn : ρ ≤ (n : ℝ≥0))
    (q K : ℝ) (hq : 0 ≤ q) (hK : 0 ≤ K) (W : ℕ → ℝ)
    (hW : ∀ i : ℕ, i ≤ m →
      ((i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) < ρ → |W i| ≤ K) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) ρ
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    |(∑ i ∈ Finset.range (m + 1), (E (v (i + 1)) - E (v i)) * W i) +
       ∑ i ∈ Finset.range m,
         let s : ℝ≥0 := (i : ℝ≥0) * Δ
         if s < ρ then q * (Δ : ℝ) * E s * W i else 0| ≤
      (m : ℝ) * ((q * (Δ : ℝ)) ^ 2 * K) + 2 * q * (Δ : ℝ) * K := by sorry
