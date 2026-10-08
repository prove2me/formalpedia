-- Prove2me | Theorems.Thm_CohenLeeSongLP_StochCentralPath_variance_mul_le
-- name    : CohenLeeSongLP.StochCentralPath.variance_mul_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T02:49:20.871133+00:00
-- url     : https://prove2.me/theorems/37582f42-08a3-4d7b-a7b7-b95f7f67a951
-- title:
--   Lemma A.1 — variance of a product of bounded random variables
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space and let $X,Y$ be (possibly dependent) real random variables with $|X|\le c_X$ and $|Y|\le c_Y$ almost surely. Then
--   $$\mathbf{Var}[XY]\le 2c_X^2\,\mathbf{Var}[Y]+2c_Y^2\,\mathbf{Var}[X].$$
--
--   In the paper this bounds the variance of the product $\mu_i^{\mathrm{new}}=(x_i+\widetilde\delta_{x,i})(s_i+\widetilde\delta_{s,i})$ in Lemma 4.8, Part 2.
--
--   **Formalization Note** $X$ and $Y$ are assumed almost-everywhere measurable, and the variance is Mathlib's `ProbabilityTheory.variance`.
-- source:
--   Cohen, Lee and Song, Solving Linear Programs in the Current Matrix Multiplication Time, J. ACM 68(1), Article 3 (2021), p. 3:32, Lemma A.1

import Mathlib

open MeasureTheory ProbabilityTheory

namespace CohenLeeSongLP.StochCentralPath

/-- Lemma A.1 (p. 3:32): for (possibly dependent) random variables with `|X| ≤ c_X` and
`|Y| ≤ c_Y` almost surely, `Var[XY] ≤ 2 c_X² Var[Y] + 2 c_Y² Var[X]`. -/
theorem variance_mul_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (cX cY : ℝ) (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
    (hXb : ∀ᵐ ω ∂P, |X ω| ≤ cX) (hYb : ∀ᵐ ω ∂P, |Y ω| ≤ cY) :
    variance (fun ω => X ω * Y ω) P ≤ 2 * cX ^ 2 * variance Y P + 2 * cY ^ 2 * variance X P := by sorry

end CohenLeeSongLP.StochCentralPath
