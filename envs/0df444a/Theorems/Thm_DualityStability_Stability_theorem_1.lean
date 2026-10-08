-- Prove2me | Theorems.Thm_DualityStability_Stability_theorem_1
-- name    : DualityStability.Stability.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:45:51.072171+00:00
-- url     : https://prove2.me/theorems/f423288f-cbe3-4aca-90c2-108d00bbdc16
-- title:
--   Theorem 1 — if f is finite at x and g is finite and continuous at Ax, then (P) is stably set and inf (P(z)) is continuous near z = 0
-- statement:
--   Let $E$ and $F$ be real locally convex Hausdorff topological vector spaces, $A : E \to F$ a continuous linear map, $f : E \to [-\infty, +\infty]$ a lower semicontinuous proper convex function and $g : F \to [-\infty, +\infty]$ an upper semicontinuous proper concave function. Consider
--
--   $$
--   (P) \qquad \text{minimize } f(x) - g(Ax) \text{ over } x \in E,
--   $$
--
--   and its perturbations $(P(z))$: minimize $f(x) - g(Ax - z)$, with $h(z) = \inf (P(z))$.
--
--   **Theorem 1.** Suppose there exists at least one $x \in E$ such that $f$ is finite at $x$, and $g$ is finite and continuous at $Ax$. Then $(P)$ is stably set, and $\inf (P(z))$ is a continuous function of $z$ in some neighbourhood of $z = 0$.
--
--   Here $(P)$ is stably set when $\inf(P) < +\infty$ and it is not the case that $\inf (P)$ is finite and every neighbourhood of $0$ contains directions $z$ along which the one-sided derivative $h'(0; z)$ is below any prescribed negative number. Theorem 1 is the paper's general constraint qualification: by the paper's main duality theorem, stability of $(P)$ is equivalent to $\inf (P) = \max (P^*)$.
--
--   **Formalization Note** Neither the statement nor the proof of Theorem 1 involves the dual spaces $E^*, F^*$, the adjoint $A^*$ or the conjugates $f^*, g^*$; these standing objects of §3 are omitted, and the theorem is stated for every pair of real locally convex Hausdorff spaces, which covers every paired setting. "Finite" is $\ne \pm\infty$; continuity of $g$ at $Ax$ is continuity of the `EReal`-valued $g$ at that point. The case $\inf (P) = -\infty$ is allowed and counts as stably set.
-- source:
--   Rockafellar, Duality and Stability in Extremum Problems Involving Convex Functions, Pacific J. Math. 21 (1967), p. 175, Theorem 1

import Mathlib
import Definitions.Def_DualityStability_Stability_ConvexFunction
import Definitions.Def_DualityStability_Stability_perturbInf
import Definitions.Def_DualityStability_Stability_StablySet

namespace DualityStability.Stability

/-- Rockafellar (1967), Theorem 1, p. 175: under the standing hypotheses of §3 (`E`, `F` real
locally convex Hausdorff spaces, `A : E → F` continuous linear, `f` l.s.c. proper convex on `E`,
`g` u.s.c. proper concave on `F`), suppose there exists at least one `x ∈ E` such that `f` is
finite at `x`, and `g` is finite and continuous at `Ax`. Then `(P)` is stably set, and
`inf (P(z))` is a continuous function of `z` in some neighborhood of `z = 0`. -/
theorem theorem_1 {E F : Type*}
    [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
    [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
    [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
    (A : E →L[ℝ] F) (f : E → EReal) (g : F → EReal)
    (hf : ProperConvexFn f) (hf_lsc : LowerSemicontinuous f)
    (hg : ProperConcaveFn g) (hg_usc : UpperSemicontinuous g)
    (hx : ∃ x : E, f x ≠ ⊥ ∧ f x ≠ ⊤ ∧ g (A x) ≠ ⊥ ∧ g (A x) ≠ ⊤ ∧ ContinuousAt g (A x)) :
    StablySet (perturbInf f g A) ∧ ∃ U ∈ nhds (0 : F), ContinuousOn (perturbInf f g A) U := by sorry

end DualityStability.Stability
