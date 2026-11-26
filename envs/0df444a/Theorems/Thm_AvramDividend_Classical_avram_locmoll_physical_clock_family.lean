-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_locmoll_physical_clock_family
-- name    : AvramDividend.Classical.avram_locmoll_physical_clock_family
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T19:06:30.823043+00:00
-- url     : https://prove2.me/theorems/08ebfa80-0d47-469d-8fa4-cb1fc6cede9b
-- title:
--   Physical reserve-band stopping clocks and exhaustion of eligible dividends
-- statement:
--   Construct the exact bounded reserve-band clocks of the parent, with arbitrary small upper bound on lower widths; prove stopping and almost-everywhere cash convergence. The closed upper boundary is a substantive stopping-time obligation, not a presumed property.
-- source:
--   Avram–Palmowski–Pistorius (2007), Proposition 4(i), exact parent d6c4b57e-8c2e-4e7b-85e3-9f961dd52d12

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_locmoll_physical_clock_family
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
      (∀ᵐ ω ∂P, Tendsto (fun k => F k ω) atTop (𝓝 (V ω))) := by sorry
