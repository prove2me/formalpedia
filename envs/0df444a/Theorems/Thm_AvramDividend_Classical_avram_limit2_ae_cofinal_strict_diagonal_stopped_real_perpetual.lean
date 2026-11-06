-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_ae_cofinal_strict_diagonal_stopped_real_perpetual
-- name    : AvramDividend.Classical.avram_limit2_ae_cofinal_strict_diagonal_stopped_real_perpetual
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T13:15:25.203+00:00
-- url     : https://prove2.me/theorems/70c9c446-632d-4e9c-ae55-2b5232f3dff0
-- title:
--   Original strict positive diagonal stopped-clock budgets give real perpetual Stieltjes dividends
-- statement:
--   For the actual original process and almost-everywhere cofinal increasing measurable ruin-stop clocks σ_k, assume one strict positive-horizon Ito cash plus nonnegative terminal expectation budget per diagonal index k on Iio(k+1), with ENNReal error_k→0. Each closed Iic(k) cash horizon is contained in the corresponding strict Iio(k+1), so the accepted original closed diagonal stopped cash bridge applies. Result: genuine full original dividendValue≤finite B, real signed Stieltjes payout L1 and exact expected real value, with time-zero/right-boundary cash atoms preserved. No invalid equality at finite horizons, terminal vanishing, law replacement or axiom.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_ae_cofinal_diagonal_stopped_vanishing_errors_real_perpetual

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_ae_cofinal_strict_diagonal_stopped_real_perpetual
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissible X x D)
    (B : ℝ≥0∞) (hB : B < ⊤)
    (σ : ℕ → Ω → ℝ≥0∞)
    (hσmeas : ∀ k : ℕ, Measurable (σ k))
    (hσmono : ∀ ω : Ω, Monotone (fun k : ℕ => σ k ω))
    (hSup : ∀ᵐ ω ∂P, (⨆ k : ℕ, σ k ω) = ruinTime X x D ω)
    (Terminal : ℕ → Ω → ℝ≥0∞) (error : ℕ → ℝ≥0∞)
    (hError : ∀ ε : ℝ≥0, 0 < ε →
      ∃ N : ℕ, ∀ k : ℕ, N ≤ k → error k ≤ (ε : ℝ≥0∞))
    (hStrictDiag : ∀ k : ℕ,
      (∫⁻ ω, ((∫⁻ t in paymentTimes (σ k ω) ∩ Iio (((k + 1 : ℕ) : ℝ)),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) + Terminal k ω) ∂P)
      ≤ B + error k) :
    dividendValue X q x D ≤ B ∧
    Integrable (fun ω : Ω =>
      ∫ t in paymentTimes (ruinTime X x D ω),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P ∧
    dividendValue X q x D =
      ENNReal.ofReal (∫ ω,
        (∫ t in paymentTimes (ruinTime X x D ω),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by sorry
