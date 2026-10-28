-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_weighted_jump_transform_from_fixed_jump_fubini
-- name    : AvramDividend.Classical.bv_weighted_jump_transform_from_fixed_jump_fubini
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T10:53:06.997996+00:00
-- url     : https://prove2.me/theorems/48636a06-08a9-4282-a79c-1c95c1044212
-- title:
--   Bounded-variation generator jump Laplace transform from exact fixed-jump identity and Fubini
-- statement:
--   Under rigorous global product integrability, the accepted fixed-negative-jump compensated Laplace transform, integrable jump exponential and small-jump coordinate, and the physical drift compensation identity, calculate the full weighted negative-jump generator transform, retaining the scale-function origin boundary W(0). This supplies the jump input to the harmonicity cancellation theorem.
-- source:
--   Avram, Palmowski and Pistorius (2007), Lemma 4. Uses the already proved fixed-jump scale-function transform and absolute Fubini lemma.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem bv_weighted_jump_transform_from_fixed_jump_fubini
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ)
    (hcont : ContinuousWithinAt W (Ici (0 : ℝ)) 0)
    (hder : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt W (deriv W x) x)
    (hDint : IntegrableOn (fun x : ℝ =>
      Real.exp (-(θ * x)) * deriv W x) (Ioi (0 : ℝ)))
    (hprod : Integrable
      (fun p : ℝ × ℝ =>
        Real.exp (-(θ * p.1)) *
          SpectrallyNegativeLevy.generatorIntegrand W p.1 p.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod
        (X.ν.restrict (Iio (0 : ℝ)))))
    (hExp : IntegrableOn (fun y : ℝ => Real.exp (θ * y) - 1)
      (Iio (0 : ℝ)) X.ν)
    (hK : IntegrableOn
      (fun y : ℝ =>
        y * (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y)
      (Iio (0 : ℝ)) X.ν)
    (hKvalue : (∫ y in Iio (0 : ℝ),
        y * (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y ∂X.ν) =
      X.c - X.drift) :
    (∫ x in Ioi (0 : ℝ),
      Real.exp (-(θ * x)) *
        (∫ y in Iio (0 : ℝ),
          SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν)) =
    (∫ y in Iio (0 : ℝ),
        Real.exp (θ * y) - 1 ∂X.ν) *
        (X.ψ θ - q)⁻¹ -
      θ * (X.c - X.drift) * (X.ψ θ - q)⁻¹ +
      (X.c - X.drift) * W 0 := by sorry

end AvramDividend.Classical
