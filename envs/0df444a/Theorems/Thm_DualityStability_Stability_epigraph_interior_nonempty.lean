-- Prove2me | Theorems.Thm_DualityStability_Stability_epigraph_interior_nonempty
-- name    : DualityStability.Stability.epigraph_interior_nonempty
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:44:39.049493+00:00
-- url     : https://prove2.me/theorems/302b5ac0-2ddc-470d-8740-1a4dde3f0c8a
-- title:
--   Proof of Theorem 1, p. 176 — the epigraph of h has a nonempty interior
-- statement:
--   Under the standing setting ($E, F$ real locally convex Hausdorff spaces, $A : E \to F$ continuous linear, $f$ l.s.c. proper convex on $E$, $g$ u.s.c. proper concave on $F$) and the hypothesis of Theorem 1 (some $x$ with $f$ finite at $x$, $g$ finite and continuous at $Ax$), let $h(z) = \inf_x \{f(x) - g(Ax - z)\}$. Then:
--
--   1. the set
--   $$
--   G = \{(y, \mu) \mid y \in F,\ g(y) \ge \mu > -\infty\} \subseteq F \times \mathbb{R}
--   $$
--   has a nonempty interior;
--   2. for every $(x, \lambda)$ in the epigraph of $f$ (that is, $\lambda \in \mathbb{R}$, $f(x) \le \lambda$), the set
--   $$
--   \{(Ax - y, \lambda - \mu) \mid \mu \le g(y)\} = (Ax, \lambda) - G
--   $$
--   is contained in the epigraph $\{(z, \nu) \mid \nu \in \mathbb{R},\ h(z) \le \nu\}$ of $h$;
--   3. the epigraph of $h$ has a nonempty interior in $F \times \mathbb{R}$.
--
--   A nonempty interior of the epigraph is, for a convex function, the criterion for continuity on the interior of the effective domain used in the next step of the proof.
-- source:
--   Rockafellar, Duality and Stability in Extremum Problems Involving Convex Functions, Pacific J. Math. 21 (1967), p. 176, proof of Theorem 1 (the sets G and (Ax, λ) − G)

import Mathlib
import Definitions.Def_DualityStability_Stability_ConvexFunction
import Definitions.Def_DualityStability_Stability_perturbInf

namespace DualityStability.Stability

/-- Rockafellar (1967), p. 176 (proof of Theorem 1): under the standing hypotheses of §3 and the
hypothesis of Theorem 1,
1. the hypograph `G = {(y, μ) | y ∈ F, g(y) ≥ μ > −∞}` of `g` (with `μ` real) has a nonempty
   interior in `F × ℝ`;
2. for any `(x, λ)` in the epigraph of `f`, the set `(Ax, λ) − G = {(Ax − y, λ − μ) | μ ≤ g(y)}` is
   contained in the epigraph `{(z, ν) | h(z) ≤ ν}` of `h(z) = inf (P(z))`;
3. the epigraph of `h` has a nonempty interior. -/
theorem epigraph_interior_nonempty {E F : Type*}
    [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
    [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
    [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
    (A : E →L[ℝ] F) (f : E → EReal) (g : F → EReal)
    (hf : ProperConvexFn f) (hf_lsc : LowerSemicontinuous f)
    (hg : ProperConcaveFn g) (hg_usc : UpperSemicontinuous g)
    (hx : ∃ x : E, f x ≠ ⊥ ∧ f x ≠ ⊤ ∧ g (A x) ≠ ⊥ ∧ g (A x) ≠ ⊤ ∧ ContinuousAt g (A x)) :
    (interior {p : F × ℝ | (p.2 : EReal) ≤ g p.1}).Nonempty ∧
      (∀ (x : E) (lam : ℝ), f x ≤ (lam : EReal) →
        (fun p : F × ℝ => ((A x, lam) : F × ℝ) - p) '' {p : F × ℝ | (p.2 : EReal) ≤ g p.1} ⊆
          {q : F × ℝ | perturbInf f g A q.1 ≤ (q.2 : EReal)}) ∧
      (interior {q : F × ℝ | perturbInf f g A q.1 ≤ (q.2 : EReal)}).Nonempty := by sorry

end DualityStability.Stability
