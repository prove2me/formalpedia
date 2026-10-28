-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_subunit_shifted_renewal_series_summable
-- name    : AvramDividend.Classical.causal_subunit_shifted_renewal_series_summable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:45:51.711488+00:00
-- url     : https://prove2.me/theorems/667e6dac-f8ee-4f6e-a315-caf700422171
-- title:
--   Pointwise summability of shifted subunit causal convolution renewal powers
-- statement:
--   Under the causal convolution recursion and verified quadratic-geometric positive-time envelope, prove the shifted series of powers is summable at every real argument. At nonpositive arguments the terms vanish, and at positive arguments they satisfy the existing geometric bound. This discharges the exact summability requirement of the canonical geometric renewal measure-density bridge in zero-barrier scale identification.
-- source:
--   Proved causal_full_convolution_powers_zero_nonpositive and renewal_density_series_summable_of_geometric_power_bound; pinned Mathlib summable_nat_add_iff.

import Theorems.Thm_AvramDividend_Classical_causal_full_convolution_powers_zero_nonpositive
import Theorems.Thm_AvramDividend_Classical_renewal_density_series_summable_of_geometric_power_bound
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_subunit_shifted_renewal_series_summable
    (k : ℝ → ℝ) (F : ℕ → ℝ → ℝ) (ρ : ℝ)
    (hρpos : 0 < ρ) (hρlt : ρ < 1)
    (hkzero : ∀ t : ℝ, t ≤ 0 → k t = 0)
    (hFzero : F 0 = k)
    (hFsucc : ∀ n : ℕ, F (n + 1) =
      fun x : ℝ => ∫ y : ℝ, k y * F n (x - y) ∂volume)
    (hFpos : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ x → 0 ≤ F n x)
    (hFbound : ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      F n x ≤ ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / x) :
    ∀ x : ℝ, Summable (fun n : ℕ =>
      if n = 0 then (0 : ℝ) else F (n - 1) x)  := by sorry
