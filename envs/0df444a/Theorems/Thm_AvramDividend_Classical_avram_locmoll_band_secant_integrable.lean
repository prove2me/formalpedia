-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_locmoll_band_secant_integrable
-- name    : AvramDividend.Classical.avram_locmoll_band_secant_integrable
-- status  : Open
-- author  : @WillR
-- created : 2026-11-27T00:19:12.163926+00:00
-- url     : https://prove2.me/theorems/e51817e1-8296-4f73-bf64-0d6a3d691529
-- title:
--   The actual eligible signed secant integrand is integrable on the stopped measure
-- statement:
--   The actual eligible signed secant integrand is integrable on the stopped measure
-- source:
--   Exact atomic diffuse secant integral b980c2dc-b50f-4bb4-b148-7f7a2859258e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_locmoll_band_secant_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (H : ℝ≥0)
    (g : ℝ → ℝ) (hg : ContDiff ℝ 2 g) (R : ℝ) (hq : 0 ≤ q)
    (hband : ∀ s : ℝ≥0, s ≤ H → (s = 0 ∨ (s : ℝ≥0∞) < ruinTime X x D ω) →
      riskProcess X x D s ω ∈ Icc 0 R ∧ x + X.X s ω - rightLimit D s ω ∈ Icc 0 R) :
    let S : Set ℝ := paymentTimes (ruinTime X x D ω) ∩ Iic (H : ℝ)
    let μ := (dividendMeasure D ω).restrict S
    let Q : ℝ → ℝ → ℝ := fun a b => if a = b then deriv g a else (g a - g b) / (a - b)
    let F : ℝ → ℝ := fun t => Real.exp (-(q * t)) *
      (1 - Q (riskProcess X x D t.toNNReal ω)
        (x + X.X t.toNNReal ω - rightLimit D t.toNNReal ω))
    Integrable F μ := by sorry
