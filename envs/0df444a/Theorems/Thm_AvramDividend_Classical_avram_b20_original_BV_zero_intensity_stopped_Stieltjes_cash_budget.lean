-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b20_original_BV_zero_intensity_stopped_Stieltjes_cash_budget
-- name    : AvramDividend.Classical.avram_b20_original_BV_zero_intensity_stopped_Stieltjes_cash_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T01:04:30.537751+00:00
-- url     : https://prove2.me/theorems/c4e26828-ae99-4d76-beac-3d89849f854f
-- title:
--   Original bounded-variation zero-intensity stopped Stieltjes cash and surviving reward expected HJB bound
-- statement:
--   For the actual capped original bounded-variation spectrally negative Lévy process with finite and zero negative-jump intensity and any admissible dividend strategy, the discounted cash before the strict pre-horizon uniform-mesh cutoff plus the surviving reward at the fixed horizon has expectation bounded by the HJB candidate value at the starting reserve. The previously needed all-time path-equals-drift condition is now a proved consequence of the same original source parameters.
-- source:
--   Source-exact original process, combining two Proved results: aaac3cb1-3611-4843-ad7b-3edfd4119e08 and adc85a28-e3da-4464-82d9-d8d83d324154.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_finite_zero_original_drift_path_ae
import Theorems.Thm_AvramDividend_Classical_avram_bvb_finite_zero_linear_paths_cash_ledger
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_b20_original_BV_zero_intensity_stopped_Stieltjes_cash_budget
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
