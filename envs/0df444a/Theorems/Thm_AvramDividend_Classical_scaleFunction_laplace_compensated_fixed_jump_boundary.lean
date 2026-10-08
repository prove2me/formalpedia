-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_laplace_compensated_fixed_jump_boundary
-- name    : AvramDividend.Classical.scaleFunction_laplace_compensated_fixed_jump_boundary
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T23:14:02.987612+00:00
-- url     : https://prove2.me/theorems/71354cf5-38e0-4d49-8193-4705e2c7c9c9
-- title:
--   Compensated scale-function jump transform with the origin boundary term
-- statement:
--   Under integrable weighted derivative and regularity hypotheses, combine the fixed-y compensated scale-function Laplace transform and the correct integration-by-parts formula to derive ∫_{x>0}e^{-θx}ΔW(x,y)dx=[e^{θy}−1−θy1_{(-1,1)}(y)]/(ψ(θ)−q)+W(0)y1_{(-1,1)}(y). It isolates the boundary contribution W(0) at the origin. Crucially the equality holds separately for each fixed jump y; the W(0)y compensation term cannot be separately integrated against an infinite-variation Lévy measure. The proof uses the two independently authored, remotely verified or in-progress child theorems as formal dependencies; until both are Proved, a sketch verdict will not discharge this target.
-- source:
--   Correct boundary bookkeeping for fixed negative-jump Laplace transforms in the scale-function Lévy generator identity, a preparatory step for Lemma 4.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_laplace_compensated_fixed_jump_boundary
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ y : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ) (hy : y ≤ 0)
    (hcont : ContinuousWithinAt W (Ici (0 : ℝ)) 0)
    (hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt W (deriv W x) x)
    (hDint : IntegrableOn (fun x : ℝ =>
       Real.exp (-(θ * x)) * deriv W x) (Ioi (0 : ℝ))) :
    (∫ x in Ioi (0 : ℝ),
       Real.exp (-(θ * x)) *
         SpectrallyNegativeLevy.generatorIntegrand W x y) =
      (Real.exp (θ * y) - 1 -
        θ * (y * (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y)) *
        (X.ψ θ - q)⁻¹ +
      (y * (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y) * W 0 := by sorry

end AvramDividend.Classical
