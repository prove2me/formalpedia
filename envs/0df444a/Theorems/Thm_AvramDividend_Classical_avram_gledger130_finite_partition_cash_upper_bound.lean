-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger130_finite_partition_cash_upper_bound
-- name    : AvramDividend.Classical.avram_gledger130_finite_partition_cash_upper_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T17:51:37.922433+00:00
-- url     : https://prove2.me/theorems/30ab679c-b670-482b-9fad-66039483f7d4
-- title:
--   Finite strict stopped cash is bounded by initial atom, actual interior cells, and final strip
-- statement:
--   For a finite nonnegative Stieltjes integral over actual strictly pre-stop payment times, an increasing stopped mesh, interior cells supported on payment times, and a larger final strip, the total cash is at most the initial payment atom plus unrestricted interior-cell cash plus strip cash. The integrability hypotheses justify taking real values rather than extended nonnegative reals.
-- source:
--   Derived directly from Proved gledger108 real chronological cash partition and measure monotonicity. Necessary for applying gledger112 pathwise cell budgets to original paymentTimes stopped cash.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger130_finite_partition_cash_upper_bound
    (μ : Measure ℝ) (f : ℝ → ℝ≥0∞) (S : Set ℝ)
    (hS : MeasurableSet S) (hSnonneg : ∀ s ∈ S, 0 ≤ s)
    (v : ℕ → ℝ) (hv : Monotone v) (hv0 : v 0 = 0)
    (k : ℕ) (ρ : ℝ) (hvk : v k < ρ)
    (hstop : v (k + 1) = ρ)
    (hcell : ∀ i < k, Ioc (v i) (v (i + 1)) ⊆ S)
    (hfinite : (∫⁻ s in S ∩ Iio ρ, f s ∂μ) < ⊤)
    (U : Set ℝ)
    (hfinal : S ∩ Ioo (v k) ρ ⊆ U)
    (hUfin : (∫⁻ s in U, f s ∂μ) ≠ ⊤) :
    (∫⁻ s in S ∩ Iio ρ, f s ∂μ).toReal ≤
      (∫⁻ s in S ∩ {0}, f s ∂μ).toReal +
      (∑ i ∈ Finset.range k,
        (∫⁻ s in Ioc (v i) (v (i + 1)), f s ∂μ).toReal) +
      (∫⁻ s in U, f s ∂μ).toReal := by sorry
