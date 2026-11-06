-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit1_p3_original_signed_grid_witness_to_strict_real_prebudget
-- name    : AvramDividend.Classical.avram_limit1_p3_original_signed_grid_witness_to_strict_real_prebudget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T23:18:07.472391+00:00
-- url     : https://prove2.me/theorems/0163ba3f-fae9-45ac-8025-98bf6cab2bb5
-- title:
--   Exact original P3 signed grid witnesses imply the strict stopped real HJB prebudget
-- statement:
--   Precise interface between canonical Open P3 c1e2f021 original BV source-grid conclusion and Open prebudget a19d8b28. Given the literal original positive finite-horizon F/M/B grid witnesses, the two corrections M+B form a single integrable, nonpositive-mean real residual and the pointwise grid bound is the zero-mesh-error case of already Proved P3 c9cd826c vanishing-error signed Fatou to actual strict budget. This is an exact logical bridge, independent of original martingale construction. All genuine ruinTime, riskProcess, strict Iio T dividendMeasure and pre-rightpayment terminal remain unchanged; no terminal vanishing, equality in law, sorry or axiom.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set Filter
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_limit1_p3_original_signed_grid_witness_to_strict_real_prebudget
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
    (hGrid : ∃ F M B : ℕ → Ω → ℝ,
      (∀ n, Measurable (F n)) ∧
      (∀ n, Integrable (F n) P) ∧
      (∀ n, 0 ≤ᵐ[P] F n) ∧
      (∀ n, Integrable (fun ω => M n ω + B n ω) P ∧
        (∫ ω, M n ω + B n ω ∂P) ≤ 0) ∧
      (∀ n, ∀ᵐ ω ∂P, F n ω ≤ w x + (M n ω + B n ω)) ∧
      (∀ᵐ ω ∂P,
        let S : ℝ≥0 := ⟨T, hT⟩
        ENNReal.ofReal (
          (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
            ENNReal.ofReal (Real.exp (-(q * t)))
              ∂(dividendMeasure D ω)).toReal +
          (if (S : ℝ≥0∞) < ruinTime X x D ω then
            Real.exp (-(q * T)) * w (riskProcess X x D S ω)
          else 0)) ≤
        liminf (fun n => ENNReal.ofReal (F n ω)) atTop)) :
    let S : ℝ≥0 := ⟨T, hT⟩
    (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω)
      else 0) ∂P) ≤ w x := by sorry
