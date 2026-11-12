-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger118_original_crossing_contact_and_strict_final_cash_bound
-- name    : AvramDividend.Classical.avram_gledger118_original_crossing_contact_and_strict_final_cash_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T14:30:55.431207+00:00
-- url     : https://prove2.me/theorems/aa6d578f-691e-4213-8080-0614d7e7c44a
-- title:
--   Original stopped crossing contact and strictly prior final-cell cash fit the last strip
-- statement:
--   At the original bounded stopping time, the last crossing-cell contact and the terminal right-payment correction are nonpositive together. The actual cash strictly inside that cell is bounded by the final shrinking strip. Finiteness permits the extended-nonnegative comparison to pass into real-valued stopped cash, excluding any payment exactly at the stop.
-- source:
--   Exact final stopped crossing atom of root-connected original Gaussian dividend-contact ledger gledger81.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gledger84_original_strict_final_cell_cash_mono
import Theorems.Thm_AvramDividend_Classical_avram_gledger86_original_terminal_payment_cancel
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger118_original_crossing_contact_and_strict_final_cash_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (q : ℝ) (ρ δ a : ℝ≥0)
    (ha : (ρ : ℝ) - (δ : ℝ) ≤ (a : ℝ)) (hab : a ≤ ρ)
    (hDiv : rightLimit D a ω ≤ D ρ ω)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hTopCap : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hfinite : (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
        Ioo ((ρ : ℝ) - (δ : ℝ)) (ρ : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s)))
      ∂(dividendMeasure D ω)) ≠ ⊤) :
    Real.exp (-(q * (ρ : ℝ))) *
      ((w (x + X.X ρ ω - rightLimit D ρ ω) -
          w (x + X.X ρ ω - rightLimit D a ω)) +
        (w (riskProcess X x D ρ ω) -
          w (x + X.X ρ ω - rightLimit D ρ ω))) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Ioo (a : ℝ) (ρ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal ≤
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
          Ioo ((ρ : ℝ) - (δ : ℝ)) (ρ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal := by sorry
