-- Prove2me | Theorems.Thm_DRSub4633_lemma_3_2_i
-- name    : DRSub4633.lemma_3_2_i
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T23:58:08.331312+00:00
-- url     : https://prove2.me/theorems/ed89c251-114c-41c4-bd88-e8ed1a750253
-- title:
--   Lemma 3.2(i) — concavity along sign-definite directions and the tangent inequality
-- statement:
--   Let $f:[0,1]^d\to\mathbb R$ be continuously differentiable and DR-submodular.
--
--   1. If $x,\ x+v\in[0,1]^d$ and either $v\ge 0$ or $v\le 0$ (coordinatewise), then $r\mapsto f(x+rv)$ is concave on $[0,1]$.
--   2. For comparable $x,y\in[0,1]^d$ (that is, $x\le y$ or $y\le x$),
--   $$f(y)\le f(x)+\langle\nabla f(x),\,y-x\rangle .$$
--
--   These are the basic consequences of DR-submodularity used throughout the comparison argument.
--
--   Differences from the source:
--   - encoding: objective defined on Q only; R^n with coordinatewise order; C^1 with boundary derivatives the continuous extensions of interior ones → f a total function on EuclideanSpace ℝ (Fin n), hypotheses on the cube only, values off the cube never read; the order written coordinatewise; GeomDRSub.IsDRSubmodular (ContDiffOn ℝ 1 on the cube, fderivWithin the cube); reason: Lean convention; on the cube the within-cube derivative of a C^1 function is the continuous extension of the interior derivative, so the instances are the same
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Lemma 3.2(i), p.8

import Mathlib
import Definitions.Def_GeomDRSub_IsDRSubmodular
import Definitions.Def_GeomDRSub_gradQ

namespace DRSub4633

/-- **Lemma 3.2(i) (Consequences of DR-submodularity).** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Lemma 3.2(i), p.8: "Let
`f : [0, 1]^d → ℝ` be `C¹` and DR-submodular. (i) If `x, x + v ∈ [0, 1]^d` and either `v ≥ 0` or
`v ≤ 0`, then `r ↦ f(x + rv)` is concave on `[0, 1]`. In particular, `f(y) ≤ f(x) + ⟨∇f(x), y − x⟩`
for comparable `x, y ∈ [0, 1]^d`."

**Formalization Note.** `C¹` and DR-submodular is `GeomDRSub.IsDRSubmodular` (continuously
differentiable on the cube, derivatives within the cube); `∇f` is `GeomDRSub.gradQ`. Vector
inequalities are coordinatewise; "comparable" means `x ≤ y` or `y ≤ x`. -/
theorem lemma_3_2_i {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : GeomDRSub.IsDRSubmodular f) :
    (∀ x v : EuclideanSpace ℝ (Fin d), x ∈ GeomDRSub.cube d → x + v ∈ GeomDRSub.cube d →
      ((∀ i, 0 ≤ v i) ∨ (∀ i, v i ≤ 0)) →
      ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (fun r : ℝ => f (x + r • v))) ∧
    (∀ x ∈ GeomDRSub.cube d, ∀ y ∈ GeomDRSub.cube d, ((∀ i, x i ≤ y i) ∨ (∀ i, y i ≤ x i)) →
      f y ≤ f x + inner ℝ (GeomDRSub.gradQ f x) (y - x)) := by sorry

end DRSub4633
