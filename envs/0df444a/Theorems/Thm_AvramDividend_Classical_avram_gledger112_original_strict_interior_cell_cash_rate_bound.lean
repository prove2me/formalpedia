-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger112_original_strict_interior_cell_cash_rate_bound
-- name    : AvramDividend.Classical.avram_gledger112_original_strict_interior_cell_cash_rate_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T14:01:09.298513+00:00
-- url     : https://prove2.me/theorems/d07ea867-35f2-4420-a09b-3f94256934a8
-- title:
--   Original pre-stop contact cells and cash have bounded discounted mesh rate
-- statement:
--   The original path's strictly pre-stop finite-cell dividend cash plus postpayment contact decrements is bounded by q times the maximum cell width times exp(qn) times actual original strictly stopped discounted dividend cash. This isolates interior cells only, assumes their true lower reserve bound, uses the exact original dividendMeasure, and excludes the initial and terminal boundary atoms. It combines the independently proved gledger99 contact bound with gledger109 real-cell partition and gledger106 ruin-clipped cash comparison.
-- source:
--   Necessary strict-interior positive-stop subledger in 16e988d7: gledger99 bounds interior contact and cash by rate×finite-cell masses, then gledger109 eliminates overcounting and gledger106 bounds strict unweighted mass by original discounted cash. Excludes zero-time and crossing terms so is strictly smaller than final positive-part cash correction.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gledger99_original_interior_contact_cells_sum_bound
import Theorems.Thm_AvramDividend_Classical_avram_gledger94_original_dividend_cell_measure_finite
import Theorems.Thm_AvramDividend_Classical_avram_gledger109_monotone_finite_cell_real_mass_partition
import Theorems.Thm_AvramDividend_Classical_avram_gledger106_original_ruinclipped_strict_mass_le_cash
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger112_original_strict_interior_cell_cash_rate_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (n ρ δ : ℝ≥0) (hρn : ρ ≤ n)
    (hρruin : (ρ : ℝ≥0∞) ≤ ruinTime X x D ω)
    (u : ℝ) (hu : 0 ≤ u)
    (hprefix : ∀ t : ℝ≥0, 0 < t → t < ρ →
      u ≤ riskProcess X x D t ω)
    (v : ℕ → ℝ≥0) (hv : Monotone v) (hv0 : v 0 = 0)
    (k : ℕ) (hvk : v k < ρ)
    (hinterior : ∀ i : ℕ, i < k → v (i + 1) < ρ)
    (hwidth : ∀ i : ℕ, i < k →
      (v (i + 1) : ℝ) - (v i : ℝ) ≤ (δ : ℝ))
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hTopCap : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) :
    (Finset.sum (Finset.range k) (fun i =>
      (∫⁻ s in Ioc (v i : ℝ) (v (i + 1) : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal +
      Real.exp (-(q * (v (i + 1) : ℝ))) *
        (w (x + X.X (v (i + 1)) ω - rightLimit D (v (i + 1)) ω) -
         w (x + X.X (v (i + 1)) ω - rightLimit D (v i) ω)))) ≤
    q * (δ : ℝ) * Real.exp (q * (n : ℝ)) *
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal := by sorry
