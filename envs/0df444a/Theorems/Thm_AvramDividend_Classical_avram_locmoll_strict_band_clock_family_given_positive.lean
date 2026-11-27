-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_locmoll_strict_band_clock_family_given_positive
-- name    : AvramDividend.Classical.avram_locmoll_strict_band_clock_family_given_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T21:51:33.351805+00:00
-- url     : https://prove2.me/theorems/1956f1aa-dda2-5052-8723-910f7fb63181
-- title:
--   Physical band exhaustion using strict positive pre-ruin postpayment paths
-- statement:
--   Physical band exhaustion using strict positive pre-ruin postpayment paths
-- source:
--   Strict-band clock family: given proved positivity on the entire bounded pre-ruin prefix.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_locmoll_strict_band_clock_family_given_positive
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (C : ℝ≥0∞)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T)
    (η : ℝ) (hη : 0 < η)
    (hpos : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ T.toNNReal →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 < x + X.X t ω - rightLimit D t ω) :
    ∃ (δ R : ℕ → ℝ) (θ : ℕ → Ω → ℝ≥0),
      (∀ k, 0 < δ k ∧ δ k < x ∧ x < R k) ∧
      (∀ k, δ k ≤ η) ∧
      Tendsto δ atTop (𝓝 0) ∧ Tendsto R atTop atTop ∧
      (∀ k ω, θ k ω ≤ T.toNNReal) ∧
      (∀ k ω t, t < θ k ω →
        x + X.X t ω - rightLimit D t ω ∈ Icc (δ k) (R k)) ∧
      (∀ k, IsStoppingTime 𝓕.rightCont
        (fun ω => (θ k ω : WithTop ℝ≥0))) ∧
      let F : ℕ → Ω → ℝ≥0∞ := fun k ω =>
        ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (θ k ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)
      let V : Ω → ℝ≥0∞ := fun ω =>
        ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)
      (∀ k, AEMeasurable (F k) P) ∧
      (∀ᵐ ω ∂P, Tendsto (fun k => F k ω) atTop (𝓝 (V ω))) := by sorry
