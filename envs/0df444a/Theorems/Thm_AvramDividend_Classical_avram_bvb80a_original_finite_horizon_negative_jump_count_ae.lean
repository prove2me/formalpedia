-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb80a_original_finite_horizon_negative_jump_count_ae
-- name    : AvramDividend.Classical.avram_bvb80a_original_finite_horizon_negative_jump_count_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:19:48.880382+00:00
-- url     : https://prove2.me/theorems/96d4b072-bfe0-421a-a497-8932dfe320a5
-- title:
--   Original finite-activity genuine negative marked count is finite before any deterministic positive real horizon
-- statement:
--   For the actual negative-jump counting measure of the original finite-activity spectrally negative Levy process, the full marked count within the genuine physical interval (0,T] and negative marks is finite almost surely. The result uses no artificial grid or postpayment reserve and directly instantiates the Proved bounded-clock finite-count theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_b199_original_bounded_physical_random_clock_fullnegative_poisson_finite_ae
open Set MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb80a_original_finite_horizon_negative_jump_count_ae
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
    (hIntensityPositive : 0 < X.ν (Iio (0 : ℝ)))
    (hCapTop : C = ⊤) :
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {t : ℝ≥0 |
        0 < t ∧ X.X t ω -
          Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ≠ 0}).map
        (fun t : ℝ≥0 => (t, X.X t ω -
          Function.leftLim (fun s : ℝ≥0 => X.X s ω) t)))
    ∀ᵐ ω ∂P, NX ω (Ioc (0 : ℝ≥0) S ×ˢ Iio (0 : ℝ)) < ⊤ := by sorry
