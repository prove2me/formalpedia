-- Prove2me | Theorems.Thm_ConvStochDual_Existence_theorem_25
-- name    : ConvStochDual.Existence.theorem_25
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:30:56.920572+00:00
-- url     : https://prove2.me/theorems/f359d575-5e79-438a-a4b8-f4432cfb9f5e
-- title:
--   Theorem 25, p. 19 — regular dual multipliers match a strong dual candidate
-- statement:
--   Under Assumption 23, every strong dual pair $(p,y)\in\mathcal X_a^\circ\times\mathcal U^*$ can be matched by an ordinary dual feasible pair $(\tilde p,\tilde y)\in\mathcal X_a^\perp\times\mathcal Y$ whose conjugate objective is no worse:
--
--   $$\varphi^*(\tilde p,\tilde y)-\langle\bar u,\tilde y\rangle\le\varphi^*(p,y)-\langle\bar u,y\rangle.$$
--
--   The theorem is the reduction from topological dual variables, including singular functionals, to random-variable dual variables.
--
--   **Formalization Note** $Ef$ is assumed proper and strongly lower semicontinuous, an additional condition needed by the argument's use of Theorem 65. The ordinary pair's $\varphi^*$ is evaluated through its integral pairing.
-- source:
--   Pennanen & Perkkiö, Dual solutions in convex stochastic optimization, arXiv:2205.15825v1, p. 19, Theorem 25

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

/-- Pennanen–Perkkiö, arXiv:2205.15825v1, p. 19, Theorem 25. -/
theorem theorem_25 (s : Setting P τ 𝔽 ιX ιU V Y)
    (hS : Standing s) (hEf : EfProperLsc s) (hEt : CondExpClosed s)
    (hA23 : Assumption23_1 s ∧ Assumption23_2 s)
    (p : X →L[ℝ] ℝ) (hp : p ∈ XaCirc s) (y : U →L[ℝ] ℝ) :
    ∃ ptilde : V, ptilde ∈ XaPerp s ∧
      ∃ ytilde : Y,
        phiStarV s ptilde ytilde -
          ((pair P (ιU s.ubar) (ytilde : RV Ω P m) : ℝ) : EReal) ≤
            phiStar s p y - ((y s.ubar : ℝ) : EReal) := by sorry

end ConvStochDual.Existence
