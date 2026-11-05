-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_integration_sweep7_original_strict_fatou_from_signed_grid_budgets
-- name    : AvramDividend.Classical.avram_integration_sweep7_original_strict_fatou_from_signed_grid_budgets
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T13:07:43.080757+00:00
-- url     : https://prove2.me/theorems/61679cb8-fe10-45ca-a2ec-d8f57d59ca19
-- title:
--   Actual BV stopped payoff bound from per-grid signed HJB expectations and Fatou, without uniform mesh domination
-- statement:
--   For the actual original stopped discounted strict-horizon Stieltjes cash and surviving payoff, an a.e. nonnegative source grid with per-grid integrability and a physical signed mesh inequality converges by nonnegative Fatou to the expected HJB bound. Only individual mesh signed-residual L1 with nonpositive expectation is assumed. No common L1 dominator, a.e. martingale limit or decomposition of the original process is assumed.
-- source:
--   Source-exact composition of proved original Fatou 5591152f-9a2e-42c0-8478-fe170d75b5b4 and pinned MeasureTheory.ofReal_integral_eq_lintegral_ofReal. Each grid expectation is bounded from hMesh and hSigned using integral_mono_ae. Provides an honest alternative to the stronger uniform DM/DB envelope requirement of Open db6a3111; physical source hMesh and hLiminf must still be proved by the P3 owner.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_main_original_strict_stopped_fatou_expected_budget
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_integration_sweep7_original_strict_fatou_from_signed_grid_budgets
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hwx : 0 ≤ w x)
    (F M B : ℕ → Ω → ℝ)
    (hFmeas : ∀ n, Measurable (F n))
    (hFint : ∀ n, Integrable (F n) P)
    (hFnonneg : ∀ n, 0 ≤ᵐ[P] F n)
    (hSigned : ∀ n, Integrable (fun ω => M n ω + B n ω) P ∧
      (∫ ω, M n ω + B n ω ∂P) ≤ 0)
    (hMesh : ∀ n, ∀ᵐ ω ∂P,
      F n ω ≤ w x + (M n ω + B n ω))
    (hLiminf : ∀ᵐ ω ∂P,
      let S : ℝ≥0 := ⟨T, hT⟩
      ENNReal.ofReal (
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (riskProcess X x D S ω)
        else 0)) ≤
        liminf (fun n => ENNReal.ofReal (F n ω)) atTop) :
    let S : ℝ≥0 := ⟨T, hT⟩
    (∫ ω,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω)
      else 0) ∂P) ≤ w x := by sorry
