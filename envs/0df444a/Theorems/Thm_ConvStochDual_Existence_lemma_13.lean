-- Prove2me | Theorems.Thm_ConvStochDual_Existence_lemma_13
-- name    : ConvStochDual.Existence.lemma_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:30:56.206367+00:00
-- url     : https://prove2.me/theorems/97713a29-f259-4852-8d94-3f7c378a73f4
-- title:
--   Lemma 13, p. 12 — splitting an ε-subgradient of an integral functional
-- statement:
--   Let $Eh$ be a proper integral functional on a solid, decomposable Fréchet space $\mathcal U$. Write a continuous linear functional $y$ uniquely as $y=y^c+y^s$, where $y^c$ is represented by a random variable in $\mathcal Y$ and $y^s$ is singular. If $\varepsilon\ge 0$ and
--
--   $$Eh(u)\ge Eh(\bar u)+\langle u-\bar u,y\rangle-\varepsilon\quad\text{for every }u\in\mathcal U,$$
--
--   then the same inequality holds with $y^c$ in place of $y$, and
--
--   $$\langle u-\bar u,y^s\rangle\le\varepsilon\quad\text{for every }u\in\operatorname{dom}Eh.$$
--
--   The result isolates the regular and singular contributions to an approximate subgradient. The integral follows the paper's positive-part convention.
-- source:
--   Pennanen & Perkkiö, Dual solutions in convex stochastic optimization, arXiv:2205.15825v1, p. 12, Lemma 13

import Mathlib
import Definitions.Def_ConvStochDual_Existence_Setting

open MeasureTheory

namespace ConvStochDual.Existence

variable {Ω U : Type*} [MeasurableSpace Ω]
  [AddCommGroup U] [Module ℝ U] [UniformSpace U]
  [IsUniformAddGroup U] [ContinuousSMul ℝ U]
  {P : Measure Ω} [IsProbabilityMeasure P] {k : ℕ}
  {ι : U →ₗ[ℝ] RV Ω P k}
  {Y₀ : Submodule ℝ (RV Ω P k)}

/-- Pennanen–Perkkiö, arXiv:2205.15825v1, p. 12, Lemma 13. -/
theorem lemma_13 (h : Ω → (Fin k → ℝ) → EReal)
    (hS : IntegralStanding h ι Y₀) (hProper : EhProper h ι)
    (ubar : U) (y : U →L[ℝ] ℝ) (yc : Y₀) (ys : U →L[ℝ] ℝ)
    (hdecomp : IsDecomp P ι Y₀ y yc ys) (ε : ℝ) (hε : 0 ≤ ε)
    (hsub : ∀ u : U, Eh h (ι ubar) +
      ((y (u - ubar) : ℝ) : EReal) - (ε : EReal) ≤ Eh h (ι u)) :
    (∀ u : U, Eh h (ι ubar) +
      ((pair P (ι (u - ubar)) (yc : RV Ω P k) : ℝ) : EReal) -
        (ε : EReal) ≤ Eh h (ι u)) ∧
    (∀ u ∈ domEh h ι, 0 ≥ ys (u - ubar) - ε) := by sorry

end ConvStochDual.Existence
