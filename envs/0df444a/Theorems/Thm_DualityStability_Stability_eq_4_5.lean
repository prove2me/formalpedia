-- Prove2me | Theorems.Thm_DualityStability_Stability_eq_4_5
-- name    : DualityStability.Stability.eq_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:44:43.710575+00:00
-- url     : https://prove2.me/theorems/2f0017d0-4c4f-42c3-a749-c9574d9e4599
-- title:
--   (4.5) — 0 ∈ A(C) − int D ⊆ int (A(C) − D)
-- statement:
--   Let $E, F, A, f, g, C, D$ be as in the standing setting ($E, F$ real locally convex Hausdorff spaces, $A$ continuous linear, $f$ l.s.c. proper convex on $E$, $g$ u.s.c. proper concave on $F$, $C = \{f < +\infty\}$, $D = \{g > -\infty\}$). Suppose there is $x \in E$ such that $f$ is finite at $x$ and $g$ is finite and continuous at $Ax$. Then $A(C)$ intersects the interior of $D$, and
--
--   $$
--   0 \in A(C) - \operatorname{int} D \subseteq \operatorname{int}\,(A(C) - D).
--   $$
--
--   Together with (4.4) this places the origin in the interior of the effective domain of $h(z) = \inf (P(z))$.
--
--   **Formalization Note** Continuity of $g$ at $Ax$ is continuity of the $[-\infty, +\infty]$-valued function $g$ (order topology of `EReal`) at that point, not continuity of $g$ restricted to $D$.
-- source:
--   Rockafellar, Duality and Stability in Extremum Problems Involving Convex Functions, Pacific J. Math. 21 (1967), p. 176, (4.5), proof of Theorem 1 (sentence beginning on p. 175)

import Mathlib
import Definitions.Def_DualityStability_Stability_ConvexFunction
import Definitions.Def_DualityStability_Stability_perturbInf

namespace DualityStability.Stability

open scoped Pointwise

/-- Rockafellar (1967), (4.5), p. 176 (proof of Theorem 1): under the standing hypotheses of §3 and
the hypothesis of Theorem 1 (some `x` with `f` finite at `x` and `g` finite and continuous at
`Ax`), `A(C)` intersects the interior of `D`, and
`0 ∈ A(C) − int D ⊆ int (A(C) − D)`, where `C = {x | f(x) < +∞}`, `D = {y | g(y) > −∞}`. -/
theorem eq_4_5 {E F : Type*}
    [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
    [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
    [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
    (A : E →L[ℝ] F) (f : E → EReal) (g : F → EReal)
    (hf : ProperConvexFn f) (hf_lsc : LowerSemicontinuous f)
    (hg : ProperConcaveFn g) (hg_usc : UpperSemicontinuous g)
    (hx : ∃ x : E, f x ≠ ⊥ ∧ f x ≠ ⊤ ∧ g (A x) ≠ ⊥ ∧ g (A x) ≠ ⊤ ∧ ContinuousAt g (A x)) :
    (A '' {x : E | f x < ⊤} ∩ interior {y : F | ⊥ < g y}).Nonempty ∧
      (0 : F) ∈ A '' {x : E | f x < ⊤} - interior {y : F | ⊥ < g y} ∧
      A '' {x : E | f x < ⊤} - interior {y : F | ⊥ < g y} ⊆
        interior (A '' {x : E | f x < ⊤} - {y : F | ⊥ < g y}) := by sorry

end DualityStability.Stability
