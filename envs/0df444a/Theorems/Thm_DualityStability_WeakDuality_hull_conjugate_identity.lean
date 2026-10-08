-- Prove2me | Theorems.Thm_DualityStability_WeakDuality_hull_conjugate_identity
-- name    : DualityStability.WeakDuality.hull_conjugate_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:44:26.859473+00:00
-- url     : https://prove2.me/theorems/92c1eb28-aec6-4bca-8b1f-cc111f06f7a0
-- title:
--   §6, p. 180 — the conjugate of the l.s.c. hull is minus the maximand of (P*)
-- statement:
--   In the setting of the dual programs (P) and (P\*), let $h(z)=\inf(\mathrm P(z))$, let $\bar h(y)=\liminf_{z\to y}h(z)$ be its lower semicontinuous hull, and let $\bar h^*(y^*)=\sup_y\{\langle y,y^*\rangle-\bar h(y)\}$ be the conjugate of $\bar h$ on $F^*$. Then for every $y^*\in F^*$,
--   $$-\bar h^*(y^*)=\inf_y\Big\{\liminf_{z\to y}h(z)-\langle y,y^*\rangle\Big\}=\inf_z\{h(z)-\langle z,y^*\rangle\}=g^*(y^*)-f^*(A^*y^*).$$
--   So the conjugate of $\bar h$ is the negative of the maximand of (P\*).
--
--   The identity holds for every $y^*$, with no finiteness assumption, and whether $\bar h$ is proper or not. It links the perturbation function of (P) to the dual problem (P\*), which is defined independently through $f^*$, $g^*$ and $A^*$.
--
--   **Formalization Note** The three equalities are stated as a conjunction of three equations, so that each step of the computation is a separate claim. All infima and suprema are in `EReal`.
-- source:
--   Rockafellar, Duality and Stability in Extremum Problems Involving Convex Functions, Pacific J. Math. 21 (1967), p. 180, §6, proof of Theorem 6 (display after (6.2))

import Definitions.Def_DualityStability_WeakDuality_Problem

namespace DualityStability.WeakDuality

variable {E E' F F' : Type*}
variable [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
variable [AddCommGroup E'] [Module ℝ E'] [TopologicalSpace E']
  [IsTopologicalAddGroup E'] [ContinuousSMul ℝ E'] [LocallyConvexSpace ℝ E'] [T2Space E']
variable [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
variable [AddCommGroup F'] [Module ℝ F'] [TopologicalSpace F']
  [IsTopologicalAddGroup F'] [ContinuousSMul ℝ F'] [LocallyConvexSpace ℝ F'] [T2Space F']

/-- Rockafellar 1967, §6, p. 180, proof of Theorem 6: for every `y* ∈ F*`,
`-h̄*(y*) = inf_y {h̄(y) - ⟨y, y*⟩} = inf_z {h(z) - ⟨z, y*⟩} = g*(y*) - f*(A*y*)`,
so `h̄*` is the negative of the maximand of (P*). -/
theorem hull_conjugate_identity (P : Problem E E' F F') (y' : F') :
    -(P.hullConjugate y') =
        (⨅ y : F, P.hull y - (P.pairF.pair y y' : EReal)) ∧
    (⨅ y : F, P.hull y - (P.pairF.pair y y' : EReal)) =
        (⨅ z : F, P.perturbation z - (P.pairF.pair z y' : EReal)) ∧
    (⨅ z : F, P.perturbation z - (P.pairF.pair z y' : EReal)) =
        P.dualMaximand y' := by sorry

end DualityStability.WeakDuality
