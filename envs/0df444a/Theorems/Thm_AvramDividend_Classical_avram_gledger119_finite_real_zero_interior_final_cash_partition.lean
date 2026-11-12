-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger119_finite_real_zero_interior_final_cash_partition
-- name    : AvramDividend.Classical.avram_gledger119_finite_real_zero_interior_final_cash_partition
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T14:39:32.047431+00:00
-- url     : https://prove2.me/theorems/ceae74c7-de36-4023-b4d9-10436c0b2c80
-- title:
--   Finite real strict stopped cash equals zero atom plus interior cells plus strict final cell
-- statement:
--   For an original nonnegative-time dividend payment set and a first-crossing clipped grid, the strict pre-stop cash restricted integral converts exactly into a real sum of initial atom, complete interior half-open cells and the final strictly open cell, provided each local cash amount is finite. No payment at the stopped endpoint is included.
-- source:
--   Real-valued cash decomposition required for the original gledger81 contact ledger and the gledger101 finite cash/contact assembly.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gledger95_zero_atom_interior_final_cash_partition
open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger119_finite_real_zero_interior_final_cash_partition
    (μ : Measure ℝ) (f : ℝ → ℝ≥0∞)
    (S : Set ℝ) (hS : MeasurableSet S)
    (hSnonneg : ∀ s ∈ S, 0 ≤ s)
    (v : ℕ → ℝ) (hv : Monotone v) (hv0 : v 0 = 0)
    (k : ℕ) (ρ : ℝ) (hvk : v k < ρ)
    (hstop : v (k + 1) = ρ)
    (hAtom : (∫⁻ s in S ∩ {0}, f s ∂μ) ≠ ⊤)
    (hCells : ∀ i ∈ Finset.range k,
      (∫⁻ s in S ∩ Ioc (v i) (v (i + 1)), f s ∂μ) ≠ ⊤)
    (hFinal : (∫⁻ s in S ∩ Ioo (v k) ρ, f s ∂μ) ≠ ⊤) :
    (∫⁻ s in S ∩ Iio ρ, f s ∂μ).toReal =
      (∫⁻ s in S ∩ {0}, f s ∂μ).toReal +
      (∑ i ∈ Finset.range k,
        (∫⁻ s in S ∩ Ioc (v i) (v (i + 1)), f s ∂μ).toReal) +
      (∫⁻ s in S ∩ Ioo (v k) ρ, f s ∂μ).toReal := by sorry
