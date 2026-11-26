-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_locmoll_positive_physical_clock_certificate
-- name    : AvramDividend.Classical.avram_locmoll_positive_physical_clock_certificate
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T18:58:14.975816+00:00
-- url     : https://prove2.me/theorems/d6c4b57e-8c2e-4e7b-85e3-9f961dd52d12
-- title:
--   Positive reserve UBV verification via one-sided smoothing and physical reserve-band clocks
-- statement:
--   Physical right-payment reserve-band stopping clocks exhaust original eligible finite-horizon cash and have a uniform arbitrarily small slack budget. This is the substantive positive-reserve alternative to exact-ruin-clock globally integrable witnesses.
-- source:
--   Avram–Palmowski–Pistorius (2007), Proposition 4(i), localised one-sided smoothing route for cc518136-9d63-4167-8587-606274d8eec9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_locmoll_positive_physical_clock_certificate
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T) :
    ∀ η : ℝ, 0 < η →
      ∃ (δ R : ℕ → ℝ) (θ : ℕ → Ω → ℝ≥0),
        (∀ k, 0 < δ k ∧ δ k < x ∧ x < R k) ∧
        Tendsto δ atTop (𝓝 0) ∧ Tendsto R atTop atTop ∧
        (∀ k ω, θ k ω =
          (min (ENNReal.ofReal T)
            (⨅ (t : ℝ≥0)
              (_ : x + X.X t ω - rightLimit D t ω ≤ δ k ∨
                R k ≤ x + X.X t ω - rightLimit D t ω),
              (t : ℝ≥0∞))).toNNReal) ∧
        (∀ k, IsStoppingTime 𝓕.rightCont
          (fun ω => (θ k ω : WithTop ℝ≥0))) ∧
        let F : ℕ → Ω → ℝ≥0∞ := fun k ω =>
          ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (θ k ω : ℝ),
            ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)
        let V : Ω → ℝ≥0∞ := fun ω =>
          ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
            ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)
        (∀ k, AEMeasurable (F k) P) ∧
        (∀ᵐ ω ∂P, Tendsto (fun k => F k ω) atTop (𝓝 (V ω))) ∧
        (∀ k, (∫⁻ ω, F k ω ∂P) ≤ ENNReal.ofReal (w x + η)) := by sorry
