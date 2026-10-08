-- Prove2me | Theorems.Thm_DualityStability_Stability_continuousOn_interior_dom
-- name    : DualityStability.Stability.continuousOn_interior_dom
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:44:51.556377+00:00
-- url     : https://prove2.me/theorems/980610af-44d2-4500-9279-08360629ddf0
-- title:
--   Proof of Theorem 1, p. 176 — h is continuous throughout the interior of its effective domain, which contains 0
-- statement:
--   Under the standing setting ($E, F$ real locally convex Hausdorff spaces, $A : E \to F$ continuous linear, $f$ l.s.c. proper convex on $E$, $g$ u.s.c. proper concave on $F$) and the hypothesis of Theorem 1 (some $x$ with $f$ finite at $x$, $g$ finite and continuous at $Ax$), the perturbation function $h(z) = \inf_x \{f(x) - g(Ax - z)\}$ satisfies
--
--   $$
--   0 \in \operatorname{int}\{z \mid h(z) < +\infty\} \quad\text{and}\quad h \text{ is continuous on } \operatorname{int}\{z \mid h(z) < +\infty\}.
--   $$
--
--   This is the second conclusion of Theorem 1, with the neighbourhood of $0$ taken to be the interior of the effective domain (4.4).
--
--   **Formalization Note** Continuity is that of a $[-\infty, +\infty]$-valued function (order topology of `EReal`), so a function identically $-\infty$ near a point is continuous there.
-- source:
--   Rockafellar, Duality and Stability in Extremum Problems Involving Convex Functions, Pacific J. Math. 21 (1967), p. 176, proof of Theorem 1 ('Hence h is continuous throughout the interior of its effective domain (4.4), which contains the origin by (4.5).')

import Mathlib
import Definitions.Def_DualityStability_Stability_ConvexFunction
import Definitions.Def_DualityStability_Stability_perturbInf

namespace DualityStability.Stability

/-- Rockafellar (1967), p. 176 (proof of Theorem 1): under the standing hypotheses of §3 and the
hypothesis of Theorem 1, `h(z) = inf (P(z))` is continuous (as a function into `[−∞, +∞]`)
throughout the interior of its effective domain `{z | h(z) < +∞}`, which contains the origin. -/
theorem continuousOn_interior_dom {E F : Type*}
    [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
    [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
    [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
    (A : E →L[ℝ] F) (f : E → EReal) (g : F → EReal)
    (hf : ProperConvexFn f) (hf_lsc : LowerSemicontinuous f)
    (hg : ProperConcaveFn g) (hg_usc : UpperSemicontinuous g)
    (hx : ∃ x : E, f x ≠ ⊥ ∧ f x ≠ ⊤ ∧ g (A x) ≠ ⊥ ∧ g (A x) ≠ ⊤ ∧ ContinuousAt g (A x)) :
    (0 : F) ∈ interior {z : F | perturbInf f g A z < ⊤} ∧
      ContinuousOn (perturbInf f g A) (interior {z : F | perturbInf f g A z < ⊤}) := by sorry

end DualityStability.Stability
