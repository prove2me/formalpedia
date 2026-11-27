-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_locmoll_strict_band_clock_family
-- name    : AvramDividend.Classical.avram_locmoll_strict_band_clock_family
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T21:51:35.559713+00:00
-- url     : https://prove2.me/theorems/070de052-93da-4594-8ad8-f73a0aa99538
-- title:
--   Bounded strict-prefix band stopping clocks exhaust all eligible physical dividends
-- statement:
--   Bounded strict-prefix band stopping clocks exhaust all eligible physical dividends
-- source:
--   Alternative exact reduction of finite-horizon unbounded-variation verification cc518136-9d63-4167-8587-606274d8eec9; use a bounded physical clock and its strict-prefix reserve band rather than a closed upper-level hitting time.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_locmoll_strict_band_clock_family
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (C : ℝ≥0∞)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T)
    (η : ℝ) (hη : 0 < η) :
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
