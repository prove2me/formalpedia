-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_locmoll_band_secant_diffuse_integral
-- name    : AvramDividend.Classical.avram_locmoll_band_secant_diffuse_integral
-- status  : Open
-- author  : @WillR
-- created : 2026-11-27T00:19:15.218114+00:00
-- url     : https://prove2.me/theorems/63a7d670-3669-5b47-ad5b-c73c18f097ba
-- title:
--   The zero-payment part of the secant integral is precisely the physical diffuse residual
-- statement:
--   The zero-payment part of the secant integral is precisely the physical diffuse residual
-- source:
--   Exact atomic diffuse secant integral b980c2dc-b50f-4bb4-b148-7f7a2859258e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_locmoll_band_secant_diffuse_integral
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (H : ℝ≥0)
    (g : ℝ → ℝ) :
    let S : Set ℝ := paymentTimes (ruinTime X x D ω) ∩ Iic (H : ℝ)
    let U : Set ℝ := {t : ℝ | rightLimit D t.toNNReal ω = D t.toNNReal ω}
    let μ := (dividendMeasure D ω).restrict S
    let Q : ℝ → ℝ → ℝ := fun a b => if a = b then deriv g a else (g a - g b) / (a - b)
    let F : ℝ → ℝ := fun t => Real.exp (-(q * t)) *
      (1 - Q (riskProcess X x D t.toNNReal ω)
        (x + X.X t.toNNReal ω - rightLimit D t.toNNReal ω))
    (∫ t in U, F t ∂μ) =
      ∫ t in paymentTimes (ruinTime X x D ω) ∩ Ioc (0 : ℝ) (H : ℝ),
        Real.exp (-(q * t)) *
          (1 - deriv g (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t.toNNReal))
        ∂((dividendMeasure D ω).restrict U) := by sorry
