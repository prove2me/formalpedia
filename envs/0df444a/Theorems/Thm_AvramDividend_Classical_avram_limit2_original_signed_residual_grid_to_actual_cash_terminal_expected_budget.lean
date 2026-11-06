-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_original_signed_residual_grid_to_actual_cash_terminal_expected_budget
-- name    : AvramDividend.Classical.avram_limit2_original_signed_residual_grid_to_actual_cash_terminal_expected_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T14:01:39.228121+00:00
-- url     : https://prove2.me/theorems/6a13e86e-1a52-4e51-b3a5-def45c0d587a
-- title:
--   Original BV compensated real grid implies actual strict stopped dividend cash and terminal expected budget
-- statement:
--   This is a complete interface from the original signed compensator grid to the real original strict stopped dividend cash plus nonnegative surviving terminal. Genuine integrable nonnegative real F_n grids obey F_n <= B+G_n pathwise and the residual G_n has actual nonpositive expected value; the initial constant B has actual integrability and expectation B. The exact original signed strict cash.toReal plus surviving terminal is dominated in the liminf. The admitted real-grid and signed Fatou budget bound it; independently admitted pathwise finiteness of original stopped Iio T cash and nonnegative terminal convert the signed expectation into actual ENNReal cash-plus-terminal expectation. Requires no circular canonical parent, no terminal vanishing or equality-in-law.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_signed_residual_grid_to_strict_fatou_expected_budget
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_signed_expected_to_true_strict_cash_without_extra_finiteness
open MeasureTheory Set Filter
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_original_signed_residual_grid_to_actual_cash_terminal_expected_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (T : ℝ) (hT : 0 ≤ T)
    (Term : Ω → ℝ) (F G : ℕ → Ω → ℝ) (B : ℝ)
    (hFmeas : ∀ n, Measurable (F n))
    (hFint : ∀ n, Integrable (F n) P)
    (hFpos : ∀ n, ∀ᵐ ω ∂P, 0 ≤ F n ω)
    (hGint : ∀ n, Integrable (G n) P)
    (hBint : Integrable (fun _ : Ω => B) P)
    (hConst : (∫ ω : Ω, B ∂P) = B)
    (hGridPath : ∀ n, ∀ᵐ ω ∂P, F n ω ≤ B + G n ω)
    (hResidualMean : ∀ n, (∫ ω, G n ω ∂P) ≤ 0)
    (hFatou : ∀ᵐ ω ∂P,
      ENNReal.ofReal
        (((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)).toReal) + Term ω) ≤
        liminf (fun n : ℕ => ENNReal.ofReal (F n ω)) atTop)
    (hTermPos : ∀ᵐ ω ∂P, 0 ≤ Term ω) :
    (∫⁻ ω,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) + ENNReal.ofReal (Term ω) ∂P) ≤
          ENNReal.ofReal B := by sorry
