-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_locmoll_smooth_physical_stopped_cash_bound
-- name    : AvramDividend.Classical.avram_locmoll_smooth_physical_stopped_cash_bound
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T19:06:27.940097+00:00
-- url     : https://prove2.me/theorems/3adbf97f-daf6-56b1-95c5-a2b7b7c33d43
-- title:
--   Smooth stopped Itô dividend inequality on an actual bounded reserve band
-- statement:
--   Prove the actual smooth stopped Itô–Meyer inequality by centring the localised Gaussian and compensated jump terms, using the signed generator and continuous dividend drift, and charging the lower-strip slack at most once. The terminal term is nonnegative and may be discarded.
-- source:
--   Avram–Palmowski–Pistorius (2007), Proposition 4(i), exact parent d6c4b57e-8c2e-4e7b-85e3-9f961dd52d12

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_locmoll_smooth_physical_stopped_cash_bound
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
    (hclock : ∀ ω, θ ω =
      (min (ENNReal.ofReal T)
        (⨅ (t : ℝ≥0)
          (_ : x + X.X t ω - rightLimit D t ω ≤ δ ∨
            R ≤ x + X.X t ω - rightLimit D t ω),
          (t : ℝ≥0∞))).toNNReal)
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
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (θ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (g x + δ) := by sorry
