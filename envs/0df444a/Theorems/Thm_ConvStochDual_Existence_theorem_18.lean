-- Prove2me | Theorems.Thm_ConvStochDual_Existence_theorem_18
-- name    : ConvStochDual.Existence.theorem_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:30:53.103478+00:00
-- url     : https://prove2.me/theorems/1c991e13-fb56-4f28-87ba-25873eda8d3a
-- title:
--   Theorem 18, p. 15 — strong dual attainment and no duality gap
-- statement:
--   Consider the paper's extended-value stochastic program on $\mathcal X\times\mathcal U$, with value function $\varphi$. Suppose $Ef$ is proper and lower semicontinuous in the product of the strong topologies, and $\operatorname{pos}(\operatorname{dom}\varphi-(0,\bar u))$ is a closed linear subspace. Then the strong dual problem $(D_s)$ attains its maximum, and
--
--   $$\inf(SP_{\mathcal X})=\sup(D_s).$$
--
--   This gives strong duality in the full topological dual before reducing the multipliers to random-variable representatives. The support and dual objectives retain extended-real values.
-- source:
--   Pennanen & Perkkiö, Dual solutions in convex stochastic optimization, arXiv:2205.15825v1, p. 15, Theorem 18

import Mathlib
import Definitions.Def_ConvStochDual_Existence_Setting

open MeasureTheory

namespace ConvStochDual.Existence

variable {Ω X U : Type*} [MeasurableSpace Ω]
  [AddCommGroup X] [Module ℝ X] [UniformSpace X]
  [IsUniformAddGroup X] [ContinuousSMul ℝ X]
  [AddCommGroup U] [Module ℝ U] [UniformSpace U]
  [IsUniformAddGroup U] [ContinuousSMul ℝ U]
  {T n m : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
  {τ : Fin n → Fin (T + 1)}
  {𝔽 : Fin (T + 1) → MeasurableSpace Ω}
  {ιX : X →ₗ[ℝ] RV Ω P n} {ιU : U →ₗ[ℝ] RV Ω P m}
  {V : Submodule ℝ (RV Ω P n)} {Y : Submodule ℝ (RV Ω P m)}

/-- Pennanen–Perkkiö, arXiv:2205.15825v1, p. 15, Theorem 18. -/
theorem theorem_18 (s : Setting P τ 𝔽 ιX ιU V Y)
    (hS : Standing s) (hEf : EfProperLsc s)
    (hpos : LinClosed (pos ((fun q : X × U => q - (0, s.ubar)) '' domPhi s))) :
    (∃ p : X →L[ℝ] ℝ, ∃ y : U →L[ℝ] ℝ,
      ((y s.ubar : ℝ) : EReal) - phiStar s p y = valDs s) ∧
    valSPX s = valDs s := by sorry

end ConvStochDual.Existence
