-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_initial_right_dividend_atom_le_hjb
-- name    : AvramDividend.Classical.avram_ubv_hor3_original_initial_right_dividend_atom_le_hjb
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:27:49.446868+00:00
-- url     : https://prove2.me/theorems/1794a9b8-2bb3-4695-9ca0-500c9fff813b
-- title:
--   Original controlled samplewise initial right-dividend atom bounded by HJB value
-- statement:
--   For every sample path of the original controlled spectrally negative Lévy process under the source capped admissibility and right-payment HJB assumptions, the initial singleton mass of the literal dividendMeasure is at most ENNReal.ofReal(w x), even when true ruinTime is positive. No stochastic source witness, martingale expectation, n or terminal horizon is assumed. This preserves the full initial right dividend atom for subsequent positive-horizon Itô budgeting.
-- source:
--   Proved original zero-clock pointwise real Cash bound 88f472ea, source exact zero-clock real Cash equals initial atom 5514c6b0, singleton dividendMeasure 4f229f9a, dividendStrategy initial zero/right-limit monotonicity. Instantiate original τ=0,W,Cash,Term and convert to ENNReal pointwise via monotonicity. All paths; no ruinTime zero assumption.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_zero_clock_cash_pointwise_le
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_zero_clock_real_cash_eq_initial_rightatom
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_singleton_eq_rightLimit_sub
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_hor3_original_initial_right_dividend_atom_le_hjb
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (ω : Ω) :
    (dividendMeasure D ω) ({0} : Set ℝ) ≤ ENNReal.ofReal (w x) := by sorry
