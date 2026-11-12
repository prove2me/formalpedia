-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_finite_zero_linear_paths_cash_ledger
-- name    : AvramDividend.Classical.avram_bvb_finite_zero_linear_paths_cash_ledger
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T23:44:11.687308+00:00
-- url     : https://prove2.me/theorems/adc85a28-e3da-4464-82d9-d8d83d324154
-- title:
--   Zero-intensity original BV continuous and singular Stieltjes cash budget under linear paths
-- statement:
--   Given almost-sure simultaneous drift paths of original X, prove the unchanged strict pre-T-delta Stieltjes cash plus surviving terminal reward budget. Include time-zero right payment, continuous and singular D at zero wealth, simultaneous payment/ruin endpoints and C=top.
-- source:
--   Original-source deterministic ledger branch of 8a3383c9-cade-472e-af16-f5abd1465970 with pathwise premise provided by avram_bvb_finite_zero_original_drift_path_ae.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb_finite_zero_linear_paths_cash_ledger
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
        w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (hLinear : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      X.X t ω = (t : ℝ) * X.drift)
    (T : ℝ) (hT : 0 < T)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (hIntensityZero : X.ν (Iio (0 : ℝ)) = 0) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let F : ℕ → Ω → ℝ := fun n ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
    ∀ n : ℕ, (∫ ω, F n ω ∂P) ≤ w x := by sorry
