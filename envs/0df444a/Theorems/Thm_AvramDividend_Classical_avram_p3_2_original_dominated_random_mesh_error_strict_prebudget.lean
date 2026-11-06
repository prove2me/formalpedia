-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_dominated_random_mesh_error_strict_prebudget
-- name    : AvramDividend.Classical.avram_p3_2_original_dominated_random_mesh_error_strict_prebudget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:24:18.893822+00:00
-- url     : https://prove2.me/theorems/c9cc8231-561c-4a59-b82c-460bc3dd6067
-- title:
--   Actual original BV stopped cash budget from dominated a.e.-vanishing physical mesh errors
-- statement:
--   For the literal original spectrally negative BV Lévy X and actual admissible D, positive-horizon strict Iio T discounted Stieltjes cash plus surviving pre-rightpayment terminal has expectation at most w x when the physical finite-grid signed residuals have nonpositive means and the mesh errors converge a.e. to zero under an integrable envelope. Dominated convergence supplies the required expectation limit; the exact accepted original random-error Fatou bridge finishes.
-- source:
--   Use the pinned Mathlib dominated convergence theorem for real Bochner integrals on the original probability space, taking a.e. strong measurability from integrability of each Err_n. Import only fully Proved original random mesh-error theorem 338a3df9. No stochastic law proxy or canonical Open parent.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_integrable_random_mesh_error_strict_prebudget

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_dominated_random_mesh_error_strict_prebudget
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
    (hFInt : ∀ n, Integrable (F n) P)
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
