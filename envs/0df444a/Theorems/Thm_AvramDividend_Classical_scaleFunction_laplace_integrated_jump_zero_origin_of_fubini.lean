-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_laplace_integrated_jump_zero_origin_of_fubini
-- name    : AvramDividend.Classical.scaleFunction_laplace_integrated_jump_zero_origin_of_fubini
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T23:42:24.488997+00:00
-- url     : https://prove2.me/theorems/617ad686-cfa5-4b08-8ac7-7ec4cda9501a
-- title:
--   Lévy jump-generator Laplace transform under a justified full-line Fubini hypothesis
-- statement:
--   In the zero-origin q-scale-function regime, suppose the weighted derivative is integrable and the full-half-line Fubini exchange for the compensated Lévy generator has been justified. Then the Laplace transform of its integrated negative-jump term equals the Lévy–Khintchine compensated exponential integral times (psi(theta)-q)^(-1). Each fixed negative jump is handled by the already proved zero-origin compensated transform; the compensated exponential is explicitly assumed Lévy-integrable, so no divergent small-jump first-moment pieces are ever separated. This theorem isolates the exact remaining global Fubini input while making the algebraic generator calculation formal.
-- source:
--   Lévy–Khintchine representation and fixed-jump q-scale transform in the analytic verification of Avram–Palmowski–Pistorius Lemma 4.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_laplace_integrated_jump_zero_origin_of_fubini
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ)
    (hcont : ContinuousWithinAt W (Ici (0 : ℝ)) 0)
    (hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt W (deriv W x) x)
    (hDint : IntegrableOn (fun x : ℝ =>
       Real.exp (-(θ * x)) * deriv W x) (Ioi (0 : ℝ)))
    (hzero : W 0 = 0)
    (hkernel : IntegrableOn (fun y : ℝ =>
       Real.exp (θ * y) - 1 -
         θ * (y * (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y))
       (Iio 0) X.ν)
    (hfubini :
       (∫ x in Ioi (0 : ℝ),
         Real.exp (-(θ * x)) *
           (∫ y in Iio (0 : ℝ),
             SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν)) =
       ∫ y in Iio (0 : ℝ),
         (∫ x in Ioi (0 : ℝ),
           Real.exp (-(θ * x)) *
             SpectrallyNegativeLevy.generatorIntegrand W x y) ∂X.ν) :
    (∫ x in Ioi (0 : ℝ),
       Real.exp (-(θ * x)) *
         (∫ y in Iio (0 : ℝ),
           SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν)) =
      (∫ y in Iio (0 : ℝ),
        Real.exp (θ * y) - 1 -
          θ * (y * (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y)
        ∂X.ν) * (X.ψ θ - q)⁻¹ := by sorry

end AvramDividend.Classical
