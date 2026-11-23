-- Prove2me | Theorems.Thm_DualityStability_StrongDuality_Supplement_theorem_2
-- name    : DualityStability.StrongDuality.Supplement.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T08:46:11.022522+00:00
-- url     : https://prove2.me/theorems/63229fa9-41b8-49c6-a7a2-fcab9ca7ca60
-- title:
--   Theorem 2 — finite dimensions and strong consistency imply (P) is stably set
-- statement:
--   Work in the standing setting of §3: paired spaces $(E,E^*)$, $(F,F^*)$, $A:E\to F$ continuous linear with adjoint $A^*$, $f$ lower semicontinuous proper convex on $E$, $g$ upper semicontinuous proper concave on $F$, and the problem
--
--   $$
--   (P)\quad\text{minimize } f(x)-g(Ax)\text{ over }x\in E,
--   $$
--
--   with perturbation function $h(z)=\inf_x\{f(x)-g(Ax-z)\}$. Let $C$ and $D$ be the effective domains of $f$ and $g$.
--
--   **Theorem 2.** If $E$ and $F$ are finite-dimensional and (P) is strongly consistent, i.e. some $x\in E$ satisfies $x\in\operatorname{ri}C$ and $Ax\in\operatorname{ri}D$, then (P) is stably set.
--
--   Stable setting is the hypothesis of Theorem 3, so in finite dimensions strong consistency yields $\inf(P)=\max(P^*)$.
--
--   **Formalization Note** "Stably set" is the published `StablySet p.h`: $h(0)<+\infty$ and $h$ is not unstably set in the sense of (4.3).
--
--   Differences from the source:
--   - encoding: E and F finite-dimensional, ri the relative interior → `[FiniteDimensional ℝ E] [FiniteDimensional ℝ F]`, ri = `intrinsicInterior ℝ`; reason: a Hausdorff vector topology on a finite-dimensional space is the Euclidean one, so the paired topologies are the paper's; intrinsicInterior is the interior within the affine span
-- source:
--   Rockafellar, Duality and Stability in Extremum Problems Involving Convex Functions, Pacific J. Math. 21 (1967), p. 177, Theorem 2 and (4.8)

import Definitions.Def_DualityStability_StrongDuality_Supplement_StronglyConsistent

namespace DualityStability.StrongDuality.Supplement

open DualityStability.StrongDuality

variable {E E' F F' : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [TopologicalSpace E'] [AddCommGroup E'] [Module ℝ E']
  [IsTopologicalAddGroup E'] [ContinuousSMul ℝ E'] [LocallyConvexSpace ℝ E'] [T2Space E']
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  [TopologicalSpace F'] [AddCommGroup F'] [Module ℝ F']
  [IsTopologicalAddGroup F'] [ContinuousSMul ℝ F'] [LocallyConvexSpace ℝ F'] [T2Space F']

/-- Theorem 2, p. 177: if `E` and `F` are finite-dimensional and (P) is strongly
consistent, then (P) is stably set. -/
theorem theorem_2 [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (p : Program E E' F F') (hsc : StronglyConsistent p) :
    StablySet p.h := by sorry

end DualityStability.StrongDuality.Supplement
