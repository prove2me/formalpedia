-- Prove2me | Theorems.Thm_ConvStochDual_Existence_theorem_26
-- name    : ConvStochDual.Existence.theorem_26
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:30:56.660995+00:00
-- url     : https://prove2.me/theorems/c01d2a6c-02ef-4274-aeb9-93ee61b1b5ea
-- title:
--   Theorem 26, p. 20 — equality and simultaneous attainment of the dual problems
-- statement:
--   Under Assumption 23, the ordinary dual $(D)$ and the strong dual $(D_s)$ have the same extended-real optimal value:
--
--   $$\sup(D_s)=\sup(D).$$
--
--   Moreover, $(D_s)$ has an attaining pair if and only if $(D)$ has an attaining pair. The ordinary dual objective is $\langle\bar u,y\rangle-Ef^*(p,y)$, where $Ef^*$ integrates the scenario-wise conjugate.
--
--   This identifies when strong dual existence yields a dual solution represented by random variables.
--
--   **Formalization Note** $Ef$ is assumed proper and strongly lower semicontinuous, matching the hypotheses needed by Theorem 25 on which this result rests.
-- source:
--   Pennanen & Perkkiö, Dual solutions in convex stochastic optimization, arXiv:2205.15825v1, p. 20, Theorem 26

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

/-- Pennanen–Perkkiö, arXiv:2205.15825v1, p. 20, Theorem 26. -/
theorem theorem_26 (s : Setting P τ 𝔽 ιX ιU V Y)
    (hS : Standing s) (hEf : EfProperLsc s) (hEt : CondExpClosed s)
    (hA23 : Assumption23_1 s ∧ Assumption23_2 s) :
    valDs s = valD s ∧
      ((∃ p : X →L[ℝ] ℝ, ∃ y : U →L[ℝ] ℝ,
          ((y s.ubar : ℝ) : EReal) - phiStar s p y = valDs s) ↔
        (∃ p : V, p ∈ XaPerp s ∧
          ∃ y : Y, dualObj s p y = valD s)) := by sorry

end ConvStochDual.Existence
