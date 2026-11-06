-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_original_probability_real_grids_to_perpetual_value
-- name    : AvramDividend.Classical.avram_limit2_original_probability_real_grids_to_perpetual_value
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T14:11:41.927608+00:00
-- url     : https://prove2.me/theorems/2b5d121b-68b4-43ff-858b-402099d2a354
-- title:
--   Original Lévy probability-normalised finite-grid witnesses bound perpetual value
-- statement:
--   The original SpectrallyNegativeLevy record carries X.isProbability : IsProbabilityMeasure P, so the initial real constant B is integrable and has expectation B. Use that genuine field to close the missing normalisation, then take each original nonnegative integrable finite-grid witness F, integrable signed residual G of nonpositive mean, and the Fatou liminf of strict stopped cash.toReal plus surviving terminal. The Proved real-grid-to-actual-cash bridge and positive-horizon iSup value theorem yield the actual infinite-horizon dividendValue ≤ ENNReal.ofReal B with no extra probability or terminal-vanishing assumption.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_signed_residual_grid_to_actual_cash_terminal_expected_budget
import Theorems.Thm_AvramDividend_Classical_avram_limit2_uniform_strict_horizon_cash_plus_terminal_budget_to_value
open MeasureTheory Set Filter
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_original_probability_real_grids_to_perpetual_value
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissible X x D)
    (B : ℝ)
    (hGrids : ∀ n : ℕ, ∃ Term : Ω → ℝ, ∃ F G : ℕ → Ω → ℝ,
      (∀ᵐ ω ∂P, 0 ≤ Term ω) ∧
      (∀ k, Measurable (F k)) ∧
      (∀ k, Integrable (F k) P) ∧
      (∀ k, ∀ᵐ ω ∂P, 0 ≤ F k ω) ∧
      (∀ k, Integrable (G k) P) ∧
      (∀ k, ∀ᵐ ω ∂P, F k ω ≤ B + G k ω) ∧
      (∀ k, (∫ ω, G k ω ∂P) ≤ 0) ∧
      (∀ᵐ ω ∂P,
        ENNReal.ofReal
          (((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
              Iio (((n + 1 : ℕ) : ℝ)),
              ENNReal.ofReal (Real.exp (-(q * t)))
                ∂(dividendMeasure D ω)).toReal) + Term ω) ≤
          liminf (fun k : ℕ => ENNReal.ofReal (F k ω)) atTop)) :
    dividendValue X q x D ≤ ENNReal.ofReal B := by sorry
