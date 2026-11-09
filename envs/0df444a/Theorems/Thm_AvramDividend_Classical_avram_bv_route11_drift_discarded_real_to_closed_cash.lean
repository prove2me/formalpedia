-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_route11_drift_discarded_real_to_closed_cash
-- name    : AvramDividend.Classical.avram_bv_route11_drift_discarded_real_to_closed_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T11:01:19.649957+00:00
-- url     : https://prove2.me/theorems/e10fc850-1d23-41b6-a7e2-be17454179b4
-- title:
--   Generator-discarded strict-horizon BV real budget implies full closed Stieltjes cash
-- statement:
--   For the original BV risk process at a positive cap and positive horizon, an integrable centred stopped term plus a vanishing positive error suffice to bound all closed-horizon discounted dividend Stieltjes cash, with zero-clock, ruin and horizon atoms. No signed generator source B appears in the premise, preventing a hidden L1 requirement.
-- source:
--   Corrected sound original BV route using Proved physical endpoint cofinality eae70d41, nonintegrable-negative-budget strict Fatou b6c77b8b with B=0, and full inclusive atom bridge d0abbeb5. Source certificate is intentionally left as a separate substantive obligation.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_strict_physical_endpoint_cofinal_for_signed_fatou
import Theorems.Thm_AvramDividend_Classical_avram_bv_strict6_original_nonintegrable_B_vanishing_error_budget
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_original_strict_expected_to_full_atom_ennreal

open MeasureTheory Set Filter
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_bv_route11_drift_discarded_real_to_closed_cash
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 < T)
    (hDiscard :
      let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
      let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
      ∃ (M Err : ℕ → Ω → ℝ),
        (∀ n, Integrable (M n) P ∧ (∫ ω, M n ω ∂P) ≤ 0) ∧
        (∀ n, Integrable (fun ω => max (Err n ω) 0) P) ∧
        Tendsto (fun n => ∫ ω, max (Err n ω) 0 ∂P) atTop (nhds 0) ∧
        (∀ n, ∀ᵐ ω ∂P,
          (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
            ENNReal.ofReal (Real.exp (-(q * t)))
              ∂(dividendMeasure D ω)).toReal +
            (if (S : ℝ≥0∞) < ruinTime X x D ω then
              Real.exp (-(q * T)) * w (riskProcess X x D S ω)
            else 0) ≤
          w x + M n ω + max (Err n ω) 0)) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal (w x) := by sorry
