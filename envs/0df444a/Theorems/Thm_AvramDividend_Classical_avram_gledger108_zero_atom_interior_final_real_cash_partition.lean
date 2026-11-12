-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger108_zero_atom_interior_final_real_cash_partition
-- name    : AvramDividend.Classical.avram_gledger108_zero_atom_interior_final_real_cash_partition
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T13:19:19.608207+00:00
-- url     : https://prove2.me/theorems/2b314a92-2c38-447f-8921-6401dd043708
-- title:
--   Finite original stop cash partition transfers exactly to real sums
-- statement:
--   At a finite original strict stopped cash integral, the exact time-zero, interior-cell and final-open-strip partition also holds after ENNReal.toReal, because each nonnegative part has finite mass. This is the missing real-valued chronological cash partition used to close gledger81 without truncating ruin or time-zero payments.
-- source:
--   Necessary finite-real conversion of the already-Proved gledger95 original payment partition for the root-connected original Gaussian stopped contact correction 16e988d7. It does not assert an expected-reward bound.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gledger95_zero_atom_interior_final_cash_partition
open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger108_zero_atom_interior_final_real_cash_partition
    (μ : Measure ℝ) (f : ℝ → ℝ≥0∞)
    (S : Set ℝ) (hS : MeasurableSet S)
    (hSnonneg : ∀ s ∈ S, 0 ≤ s)
    (v : ℕ → ℝ) (hv : Monotone v) (hv0 : v 0 = 0)
    (k : ℕ) (ρ : ℝ) (hvk : v k < ρ)
    (hstop : v (k + 1) = ρ)
    (hfinite : (∫⁻ s in S ∩ Iio ρ, f s ∂μ) < ⊤) :
    (∫⁻ s in S ∩ Iio ρ, f s ∂μ).toReal =
      (∫⁻ s in S ∩ {0}, f s ∂μ).toReal +
      (∑ i ∈ Finset.range k,
        (∫⁻ s in S ∩ Ioc (v i) (v (i + 1)), f s ∂μ).toReal) +
      (∫⁻ s in S ∩ Ioo (v k) ρ, f s ∂μ).toReal := by sorry
