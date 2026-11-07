-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_turn8b_original_B_L1_from_true_strict_cash_budget
-- name    : AvramDividend.Classical.avram_p3_grid4_turn8b_original_B_L1_from_true_strict_cash_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T19:00:42.068759+00:00
-- url     : https://prove2.me/theorems/c52a3794-d36a-4ad3-9fa3-8a5e4669cfed
-- title:
--   Original strict BV stopped cash budget forces negative HJB-residual source to be integrable
-- statement:
--   For the literal original X/D strictly stopped dividendMeasure cash plus surviving pre-rightpayment terminal, assume exact equality of Pay to this original cash term, its almost-sure nonnegativity, an authentic physical signed HJB/residual B that is almost surely nonpositive and strongly measurable, integrable centred M, integrable positive mesh error, and the actual pathwise source bound. The negative B must be L1 by a two-sided norm squeeze. The theorem isolates the L1 bridge in 2bc848f9 and requires no global derivative bound; the missing original source bound and measurability remain genuine obligations.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid4_turn8b_original_B_L1_from_true_strict_cash_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ)
    (T : ℝ) (hT : 0 ≤ T) (S : ℝ≥0)
    (hS : S = ⟨T, hT⟩) (δ : ℕ → ℝ)
    (Pay M B Err : ℕ → Ω → ℝ)
    (hPayExact : ∀ n ω, Pay n ω =
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
         Real.exp (-(q * T)) * w (riskProcess X x D S ω)
       else 0))
    (hM : ∀ n, Integrable (M n) P)
    (hErr : ∀ n, Integrable (fun ω => max (Err n ω) 0) P)
    (hBMeas : ∀ n, AEStronglyMeasurable (B n) P)
    (hBNeg : ∀ n, ∀ᵐ ω ∂P, B n ω ≤ 0)
    (hPayPos : ∀ n, ∀ᵐ ω ∂P, 0 ≤ Pay n ω)
    (hPath : ∀ n, ∀ᵐ ω ∂P,
      Pay n ω ≤ w x + (M n ω + B n ω) + max (Err n ω) 0) :
    ∀ n, Integrable (B n) P := by sorry
