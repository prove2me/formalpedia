-- Prove2me | Theorems.Thm_DualityStability_StrongDuality_lemma_2
-- name    : DualityStability.StrongDuality.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:43:53.878063+00:00
-- url     : https://prove2.me/theorems/b125edd8-dac3-4bfd-858b-012d09bf0b99
-- title:
--   Lemma 2 — convexity of the perturbation function
-- statement:
--   Under the paired-space and proper semicontinuous convex–concave assumptions of §3, let $h(z)$ be the infimum of the perturbed primal problem:
--
--   $$
--   h(z)=\inf_{x\in E}\{f(x)-g(Ax-z)\},\qquad z\in F.
--   $$
--
--   The function $h$ is convex on $F$: its real epigraph $\{(z,\mu)\in F\times\mathbb R:h(z)\le\mu\}$ is a convex set. This establishes the convexity needed for the paper's directional derivative and stability criterion.
--
--   **Formalization Note** The epigraph formulation allows $h$ to take $-\infty$ and does not turn the assertion into an extended-real inequality with ambiguous endpoint arithmetic.
-- source:
--   Rockafellar, Duality and Stability in Extremum Problems Involving Convex Functions, Pacific J. Math. 21 (1967), p. 174, Lemma 2

import Definitions.Def_DualityStability_StrongDuality_Program

namespace DualityStability.StrongDuality

variable {E E' F F' : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [TopologicalSpace E'] [AddCommGroup E'] [Module ℝ E']
  [IsTopologicalAddGroup E'] [ContinuousSMul ℝ E'] [LocallyConvexSpace ℝ E'] [T2Space E']
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  [TopologicalSpace F'] [AddCommGroup F'] [Module ℝ F']
  [IsTopologicalAddGroup F'] [ContinuousSMul ℝ F'] [LocallyConvexSpace ℝ F'] [T2Space F']

/-- Lemma 2, p. 174: the epigraph of the perturbation function is convex. -/
theorem lemma_2 (p : Program E E' F F') : EpiConvex p.h := by sorry

end DualityStability.StrongDuality
