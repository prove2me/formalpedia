-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_dominated_error_grid_without_payoff_L1
-- name    : AvramDividend.Classical.avram_p3_2_original_dominated_error_grid_without_payoff_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:45:55.217194+00:00
-- url     : https://prove2.me/theorems/58a59b3f-5d68-4835-9808-31d4df980e7d
-- title:
--   Original BV dominated-error strict Fatou budget with automatic physical grid payoff L1
-- statement:
--   For the true original bounded-variation Lévy X and admissible dividend D, the stopped strict Iio T expected cash plus surviving pre-rightpayment terminal is bounded by w(x) from nonnegative measurable finite-grid rewards and a genuine compensated signed source with nonpositive mean and an integrable a.e.-vanishing dominated mesh error. The grid reward L1 condition is derived from the physical upper inequality and signed/error L1, not assumed.
-- source:
--   Prove ∀n Integrable F_n via 0≤F_n≤w(x)+R_n+Err_n and the genuine L1 signed/error upper envelope; then import fully Proved P3-2 original dominated random mesh-error strict budget c9cc8231. This reduces one source premise without importing Open canonical targets.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_dominated_random_mesh_error_strict_prebudget
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_dominated_error_grid_without_payoff_L1
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
    (hErrInt : ∀ n, Integrable (Err n) P)
    (H : Ω → ℝ) (hHInt : Integrable H P)
    (hDom : ∀ n, ∀ᵐ ω ∂P, ‖Err n ω‖ ≤ H ω)
    (hErrAE : ∀ᵐ ω ∂P,
      Tendsto (fun n => Err n ω) atTop (nhds (0 : ℝ)))
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
