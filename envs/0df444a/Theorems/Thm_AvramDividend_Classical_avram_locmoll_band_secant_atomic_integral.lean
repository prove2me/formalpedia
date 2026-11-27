-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_locmoll_band_secant_atomic_integral
-- name    : AvramDividend.Classical.avram_locmoll_band_secant_atomic_integral
-- status  : Open
-- author  : @WillR
-- created : 2026-11-27T00:19:10.924631+00:00
-- url     : https://prove2.me/theorems/9391a15d-7ae4-4db1-93a0-da5d719d2d4b
-- title:
--   Countable signed eligible Stieltjes atoms sum to the exact physical residual
-- statement:
--   Countable signed eligible Stieltjes atoms sum to the exact physical residual
-- source:
--   Exact atomic diffuse secant integral b980c2dc-b50f-4bb4-b148-7f7a2859258e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_locmoll_band_secant_atomic_integral
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (H : ℝ≥0)
    (g : ℝ → ℝ) (hg : ContDiff ℝ 2 g) :
    let S : Set ℝ := paymentTimes (ruinTime X x D ω) ∩ Iic (H : ℝ)
    let U : Set ℝ := {t : ℝ | rightLimit D t.toNNReal ω = D t.toNNReal ω}
    let μ := (dividendMeasure D ω).restrict S
    let Q : ℝ → ℝ → ℝ := fun a b => if a = b then deriv g a else (g a - g b) / (a - b)
    let F : ℝ → ℝ := fun t => Real.exp (-(q * t)) *
      (1 - Q (riskProcess X x D t.toNNReal ω)
        (x + X.X t.toNNReal ω - rightLimit D t.toNNReal ω))
    Integrable F μ →
    (∀ s : ℝ≥0, F (s : ℝ) * (rightLimit D s ω - D s ω) =
      Real.exp (-(q * (s : ℝ))) *
        ((rightLimit D s ω - D s ω) + g (x + X.X s ω - rightLimit D s ω) -
          g (riskProcess X x D s ω))) →
    (∫ t in Uᶜ, F t ∂μ) =
      ∑' s : ℝ≥0, if s ≤ H ∧ (s = 0 ∨ (s : ℝ≥0∞) < ruinTime X x D ω) then
        Real.exp (-(q * (s : ℝ))) *
          ((rightLimit D s ω - D s ω) + g (x + X.X s ω - rightLimit D s ω) -
            g (riskProcess X x D s ω))
      else 0 := by sorry
