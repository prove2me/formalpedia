-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_locmoll_band_grid_source_limit
-- name    : AvramDividend.Classical.avram_locmoll_band_grid_source_limit
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T23:16:01.732383+00:00
-- url     : https://prove2.me/theorems/63cea48d-742d-4228-9d6e-341d1044b67b
-- title:
--   Physical smooth stopped grid source converges along a cofinal subsequence to centred noise plus generator drift
-- statement:
--   Physical smooth stopped grid source converges along a cofinal subsequence to centred noise plus generator drift
-- source:
--   Exact physical grid decomposition of 11f1a409-adc5-538d-b8b2-be83efcb307e using 2983886e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_locmoll_band_grid_source_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (C : ℝ≥0∞) (hC : 0 < C)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T)
    (δ R : ℝ) (hδ : 0 < δ) (hδx : δ < x) (hxR : x < R)
    (θ : Ω → ℝ≥0)
    (hθle : ∀ ω, θ ω ≤ T.toNNReal)
    (hprefix : ∀ ω t, t < θ ω →
      x + X.X t ω - rightLimit D t ω ∈ Icc δ R)
    (hstop : IsStoppingTime 𝓕.rightCont (fun ω => (θ ω : WithTop ℝ≥0)))
    (g : ℝ → ℝ) (hg : ContDiff ℝ 2 g)
    (hNonneg : ∀ y : ℝ, 0 ≤ g y)
    (hZero : ∀ y : ℝ, y ≤ 0 → g y = 0)
    (hGrad : ∀ y : ℝ, δ ≤ y → 1 ≤ deriv g y)
    (hGen : ∀ y : ℝ, δ ≤ y → ENNReal.ofReal y ≤ C →
      X.GeneratorIntegrable g y ∧ X.generator g y - q * g y ≤ 0)
    (hSec : ∀ a b : ℝ, δ ≤ b → b ≤ a →
      a - b ≤ g a - g b)
    (hLoss : ∀ a b : ℝ, 0 ≤ b → b ≤ a →
      a - b ≤ g a - g b + δ) :
    let Cash : Ω → ℝ := (fun ω : Ω => (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (θ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal)
    let G : Ω → ℝ := (fun ω : Ω => ∫ t in Ioc (0 : ℝ) (θ ω : ℝ),
      Real.exp (-(q * t)) *
        (X.generator g (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t.toNNReal) -
          q * g (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t.toNNReal)))
    ∃ (m : ℕ → ℕ) (M : Ω → ℝ),
      Tendsto m atTop atTop ∧ Integrable M P ∧ (∫ ω, M ω ∂P) = 0 ∧
      let u : ℕ → ℕ → ℝ≥0 := fun n i => (i : ℝ≥0) * T.toNNReal / ((m n : ℝ≥0) + 1)
      let k : ℕ → ℕ := fun n => m n + 1
      let Source : ℕ → Ω → ℝ := fun n ω =>
        let v : ℕ → ℝ≥0 := fun i => min (u n i) (θ ω)
        let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
        let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
        let Z : ℕ → ℝ := fun i => x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
        ∑ i ∈ Finset.range (k n),
          ((E (v (i + 1)) - E (v i)) * g (Y (v i)) +
            E (v (i + 1)) * (g (Z i) - g (Y (v i))))
      ∀ᵐ ω ∂P, Tendsto (fun n => Source n ω) atTop (𝓝 (M ω + G ω)) := by sorry
