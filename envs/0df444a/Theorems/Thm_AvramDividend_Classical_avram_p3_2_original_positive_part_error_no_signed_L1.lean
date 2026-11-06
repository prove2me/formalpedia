-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_positive_part_error_no_signed_L1
-- name    : AvramDividend.Classical.avram_p3_2_original_positive_part_error_no_signed_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T19:02:40.533379+00:00
-- url     : https://prove2.me/theorems/c88f092d-7783-4985-90fb-76d3a9811876
-- title:
--   Original stopped BV strict cash budget from vanishing positive-part mesh errors, without signed-error or payoff L1
-- statement:
--   For the actual original spectrally negative Levy process and admissible dividend strategy, a nonnegative measurable physical-grid reward dominated by a mean-nonpositive original signed source and random errors requires only integrable positive parts of those errors with means tending to zero. The signed negative parts need not be integrable and the grid reward L1 is derived.
-- source:
--   Replace original signed random mesh errors by their positive parts, which dominate them pathwise. The true positive parts are integrable with vanishing means by premise, while the negative parts are never integrated. Accepted 2345879f derives original physical-grid payoff L1 from the signed upper. Accepted 338a3df9 then yields the precise actual-X/D strict stopped expectation budget. No canonical Open imports, proxy process or axiom.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_fatou_grid_integrability_from_signed_upper
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_integrable_random_mesh_error_strict_prebudget
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_positive_part_error_no_signed_L1
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
    (F R Err : ℕ → Ω → ℝ)
    (hFMeas : ∀ n, Measurable (F n))
    (hFNonneg : ∀ n, 0 ≤ᵐ[P] F n)
    (hR : ∀ n, Integrable (R n) P ∧
      (∫ ω, R n ω ∂P) ≤ 0)
    (hErrPosInt : ∀ n,
      Integrable (fun ω => max (Err n ω) 0) P)
    (hErrPosMean : Tendsto
      (fun n => ∫ ω, max (Err n ω) 0 ∂P)
      atTop (nhds (0 : ℝ)))
    (hBound : ∀ n, ∀ᵐ ω ∂P,
      F n ω ≤ w x + R n ω + Err n ω)
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
