-- Prove2me | Theorems.Thm_ALAVI_subproblem_unique
-- name    : ALAVI.subproblem_unique
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:40:27.014669+00:00
-- url     : https://prove2.me/theorems/50d52f88-ee86-4cff-859f-8536c11dd310
-- title:
--   p.13 — the primal subproblem (27) has a unique solution
-- statement:
--   Let $E,F$ be finite-dimensional real inner product spaces, $U\subseteq E$ a closed convex set, $C\subseteq F$ a closed convex cone with dual cone $C^*$, and let $G:E\to E$, $J:E\to(-\infty,+\infty]$, $\Theta:E\to F$ satisfy the standing assumptions: $G$ is $L$-Lipschitz on $U$, $J$ is proper convex l.s.c., $\Theta$ is $C$-convex and $\tau$-Lipschitz on $U$ ($\tau>0$).
--
--   Let $\alpha>0$, $g,v\in E$ and $q\in C^*$, and suppose $U\cap\operatorname{dom}J\ne\emptyset$. Then the problem
--
--   $$
--   \min_{w\in U}\ \langle g,w\rangle+J(w)+\langle q,\Theta(w)\rangle+\frac1{2\alpha}\|w-v\|^2
--   $$
--
--   has exactly one minimizer. In particular each step (27) of ALAVI is well defined, and runs of ALAVI exist.
--
--   Differences from the source:
--   - generalization: ℝⁿ and ℝᵐ with the Euclidean inner product → finite-dimensional real inner product spaces E, F; reason: ℝⁿ, ℝᵐ are instances and no coordinate is used, so the statement specializes to the page's
--   - generalization: G continuous on ℝⁿ and L-Lipschitz on U (H2); Θ continuous on ℝⁿ and τ-Lipschitz on an open O ⊇ U (H5) → G L-Lipschitz on U and Θ τ-Lipschitz on U, nothing assumed off U; reason: the proofs evaluate G and Θ only at points of U; the page's hypotheses imply these
--   - reading: J "a continuous function on U" (p.2) and "proper convex l.s.c." (H3, p.4) → J : E → (−∞, +∞] proper, convex, lower semicontinuous (IsProperConvexLSC); reason: the two printed descriptions differ; (H3) is the one the proofs use, and a convex J continuous on the closed set U, extended by +∞, satisfies it
--   - encoding: C a nonempty closed convex cone; C∗ (never defined on the page); Π the projection onto C∗ → C : ProperCone ℝ F; C∗ = ProperCone.innerDual C; Π = CalamaiMore.Convergence.proj onto C∗; reason: every nonempty closed convex cone is a ProperCone; C∗ is used as the dual cone {p | ⟨x, p⟩ ≥ 0 ∀ x ∈ C} (p.7, Example A.4); the projection onto the nonempty closed convex C∗ exists
--   - generalization: Assumption A, including (H1) S_VIP ≠ ∅ and (H6) the constraint qualification → (H1) and (H6) not assumed; a point of U ∩ dom J is assumed instead; reason: (H6) is not used in the proof, and (H1) is used only through a point of U ∩ dom J, which it supplies
--   - generalization: the data G(uᵏ), qᵏ, vᵏ of iteration k → any g, v ∈ E and q ∈ C∗; reason: every iteration of ALAVI supplies such data
--   - encoding: u = arg min_{u∈U} … (27) → the predicate IsSubproblemSol (x ∈ U minimizes the objective, computed in EReal as a real number plus J); reason: the same set of minimizers; uniqueness is stated separately
-- source:
--   Zhao, Zhu & Zhang, An Augmented Lagrangian Approach to Conically Constrained Non-monotone Variational Inequality Problems, arXiv:2306.01214v1, §4.2, p.13 ("the unique solution uᵏ⁺¹ of the primal subproblem (27)"); subproblem (27), p.12

import Mathlib
import Definitions.Def_GoldenRatioVI_Fixed_solutionSet
import Definitions.Def_CalamaiMore_Convergence_proj
import Definitions.Def_ALAVI_Standing
import Definitions.Def_ALAVI_IsSubproblemSol

namespace ALAVI

/-- **The primal subproblem (27) has a unique solution** (p.13: "the unique solution uᵏ⁺¹ of the
primal subproblem (27)"). For any `g, v ∈ E`, `α > 0` and `q ∈ C*`, if `U ∩ dom J ≠ ∅`, the
problem `min_{w ∈ U} ⟨g, w⟩ + J(w) + ⟨q, Θ(w)⟩ + (1/(2α))‖w - v‖²` has exactly one minimizer.

Zhao, Zhu & Zhang, arXiv:2306.01214v1, §4.2, p.13 (statement before (32)); subproblem (27), p.12.

Formalization Note: `g`, `q`, `v` are arbitrary (in ALAVI `g = G(uᵏ)`, `q = qᵏ ∈ C*`, `v = vᵏ`).
The point of `U ∩ dom J` excludes the case in which every point of `U` has objective `+∞`. -/
theorem subproblem_unique {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (U : Set E) (C : ProperCone ℝ F) (G : E → E) (J : E → EReal) (Θ : E → F) (L τ α : ℝ)
    (hA : Standing U C G J Θ L τ) (hα : 0 < α) (g v : E) (q : F) (hq : q ∈ ProperCone.innerDual (C : Set F))
    (hfeas : ∃ a ∈ U, a ∈ GoldenRatioVI.Fixed.effDom J) :
    ∃! x, IsSubproblemSol U J Θ α g q v x := by sorry

end ALAVI
