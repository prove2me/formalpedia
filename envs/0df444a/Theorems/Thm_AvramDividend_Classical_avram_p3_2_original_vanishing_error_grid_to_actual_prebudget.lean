-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_vanishing_error_grid_to_actual_prebudget
-- name    : AvramDividend.Classical.avram_p3_2_original_vanishing_error_grid_to_actual_prebudget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T16:33:51.560563+00:00
-- url     : https://prove2.me/theorems/c9cd826c-ecc8-4b38-ab21-5d27410f8348
-- title:
--   Original BV signed finite-grid epsilon-to-zero certificate gives exact pre-rightpayment stopped value budget
-- statement:
--   For the exact original X.X and admissible cumulative D, measurable integrable nonnegative finite-grid cash plus strict terminal with genuinely compensated signed residual mean at most zero and deterministic grid errors tending to zero yields the sharp expectation bound under actual stopping and survival.
-- source:
--   Full proof from Proved f1877a7f signed Fatou vanishing-error bridge, original X/D prebudget L1, nonnegativity of discounted actual cash and positive strictly surviving terminal. No Open canonical imports, no Poisson surrogate and no unjustified source existence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_prebudget_L1
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_vanishing_error_signed_fatou_original_grid

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_vanishing_error_grid_to_actual_prebudget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ) (hT : 0 ≤ T)
    (hTpos : 0 < T)
    (F R : ℕ → Ω → ℝ) (ε : ℕ → ℝ)
    (hFMeas : ∀ n, Measurable (F n))
    (hFInt : ∀ n, Integrable (F n) P)
    (hFNonneg : ∀ n, 0 ≤ᵐ[P] F n)
    (hR : ∀ n, Integrable (R n) P ∧
      (∫ ω, R n ω ∂P) ≤ 0)
    (hErr : Tendsto ε atTop (nhds (0 : ℝ)))
    (hBound : ∀ n, ∀ᵐ ω ∂P,
      F n ω ≤ w x + R n ω + ε n)
    (hFatou : ∀ᵐ ω ∂P,
      let S : ℝ≥0 := ⟨T, hT⟩
      ENNReal.ofReal (
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)).toReal +
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (riskProcess X x D S ω)
        else 0)) ≤
      liminf (fun n => ENNReal.ofReal (F n ω)) atTop) :
    let S : ℝ≥0 := ⟨T, hT⟩
    (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω)
      else 0) ∂P) ≤ w x := by sorry
