-- Prove2me | Theorems.Thm_DualityStability_Stability_eq_4_4
-- name    : DualityStability.Stability.eq_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:44:46.49497+00:00
-- url     : https://prove2.me/theorems/5986c524-9c66-4c21-b8c3-fdda33d7e7f3
-- title:
--   (4.4) — the effective domain of h is A(C) − D
-- statement:
--   Let $E, F$ be real locally convex Hausdorff topological vector spaces, $A : E \to F$ a continuous linear map, $f$ a lower semicontinuous proper convex function on $E$ and $g$ an upper semicontinuous proper concave function on $F$. Let $C = \{x \mid f(x) < +\infty\}$ and $D = \{y \mid g(y) > -\infty\}$ be the effective domains, and $h(z) = \inf_x \{f(x) - g(Ax - z)\}$. Then
--
--   $$
--   \{z \mid h(z) < +\infty\} = \{Ax - y \mid f(x) < +\infty,\ g(y) > -\infty\} = A(C) - D.
--   $$
--
--   This identifies the effective domain of the perturbation function with a Minkowski difference of the two effective domains, the starting point of the proof of Theorem 1.
--
--   **Formalization Note** $A(C) - D$ is the pointwise set difference `A '' C - D`.
-- source:
--   Rockafellar, Duality and Stability in Extremum Problems Involving Convex Functions, Pacific J. Math. 21 (1967), p. 175, (4.4), proof of Theorem 1

import Mathlib
import Definitions.Def_DualityStability_Stability_ConvexFunction
import Definitions.Def_DualityStability_Stability_perturbInf

namespace DualityStability.Stability

open scoped Pointwise

/-- Rockafellar (1967), (4.4), p. 175 (proof of Theorem 1): under the standing hypotheses of §3
(`f` l.s.c. proper convex on `E`, `g` u.s.c. proper concave on `F`, `A : E → F` continuous
linear), the effective domain of `h(z) = inf (P(z))` is
`{z | h(z) < +∞} = {Ax − y | f(x) < +∞, g(y) > −∞} = A(C) − D`,
where `C = {x | f(x) < +∞}` and `D = {y | g(y) > −∞}`. -/
theorem eq_4_4 {E F : Type*}
    [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
    [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
    [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
    (A : E →L[ℝ] F) (f : E → EReal) (g : F → EReal)
    (hf : ProperConvexFn f) (hf_lsc : LowerSemicontinuous f)
    (hg : ProperConcaveFn g) (hg_usc : UpperSemicontinuous g) :
    {z : F | perturbInf f g A z < ⊤} =
        {z : F | ∃ (x : E) (y : F), f x < ⊤ ∧ ⊥ < g y ∧ z = A x - y} ∧
      {z : F | perturbInf f g A z < ⊤} = A '' {x : E | f x < ⊤} - {y : F | ⊥ < g y} := by sorry

end DualityStability.Stability
