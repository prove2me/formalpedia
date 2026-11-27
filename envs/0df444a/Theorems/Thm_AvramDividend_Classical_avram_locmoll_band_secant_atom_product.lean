-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_locmoll_band_secant_atom_product
-- name    : AvramDividend.Classical.avram_locmoll_band_secant_atom_product
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-27T00:19:11.935776+00:00
-- url     : https://prove2.me/theorems/e3385360-ae74-4836-bbd2-a457d6b8855b
-- title:
--   The exact discounted secant multiplied by the actual right-payment mass is the signed atomic residual
-- statement:
--   The exact discounted secant multiplied by the actual right-payment mass is the signed atomic residual
-- source:
--   Exact atomic diffuse secant integral b980c2dc-b50f-4bb4-b148-7f7a2859258e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_locmoll_band_secant_atom_product
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (H : ℝ≥0)
    (g : ℝ → ℝ) (s : ℝ≥0) :
    let Q : ℝ → ℝ → ℝ := fun a b => if a = b then deriv g a else (g a - g b) / (a - b)
    let F : ℝ → ℝ := fun t => Real.exp (-(q * t)) *
      (1 - Q (riskProcess X x D t.toNNReal ω)
        (x + X.X t.toNNReal ω - rightLimit D t.toNNReal ω))
    F (s : ℝ) * (rightLimit D s ω - D s ω) =
      Real.exp (-(q * (s : ℝ))) *
        ((rightLimit D s ω - D s ω) + g (x + X.X s ω - rightLimit D s ω) -
          g (riskProcess X x D s ω)) := by sorry
