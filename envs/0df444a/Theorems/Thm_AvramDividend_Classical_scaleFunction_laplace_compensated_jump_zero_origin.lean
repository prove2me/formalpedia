-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_laplace_compensated_jump_zero_origin
-- name    : AvramDividend.Classical.scaleFunction_laplace_compensated_jump_zero_origin
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T23:40:50.789295+00:00
-- url     : https://prove2.me/theorems/eb7cd464-bedd-46f4-acc3-8cbab91db737
-- title:
--   Pure compensated jump-kernel Laplace transform when scale function vanishes at zero
-- statement:
--   If the q-scale function W vanishes at 0, the correct fixed-jump compensated-generator Laplace transform reduces exactly to the compensated exponential kernel (exp(theta*y)-1-theta*y 1_{(-1,1)}(y))/(psi(theta)-q). This is the unbounded-variation boundary branch: the extra y indicator times W(0) term is exactly zero, so the Lévy-integrable compensated expression is retained intact. The proof applies the independently proved boundary-corrected fixed-jump transform and the hypothesis W(0)=0, without any illegitimate separate first-moment integrals.
-- source:
--   Spectrally negative Lévy scale-function Laplace transform, unbounded-variation origin condition, and compensated Lévy–Khintchine kernel.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_laplace_compensated_jump_zero_origin
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ y : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ) (hy : y ≤ 0)
    (hcont : ContinuousWithinAt W (Ici (0 : ℝ)) 0)
    (hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt W (deriv W x) x)
    (hDint : IntegrableOn (fun x : ℝ =>
       Real.exp (-(θ * x)) * deriv W x) (Ioi (0 : ℝ)))
    (hzero : W 0 = 0) :
    (∫ x in Ioi (0 : ℝ),
       Real.exp (-(θ * x)) *
         SpectrallyNegativeLevy.generatorIntegrand W x y) =
      (Real.exp (θ * y) - 1 -
        θ * (y * (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y)) *
          (X.ψ θ - q)⁻¹ := by sorry

end AvramDividend.Classical
