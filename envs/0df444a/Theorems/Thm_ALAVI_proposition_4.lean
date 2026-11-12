-- Prove2me | Theorems.Thm_ALAVI_proposition_4
-- name    : ALAVI.proposition_4
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T11:40:30.182015+00:00
-- url     : https://prove2.me/theorems/20e2f722-1cfa-41d2-9241-4d0369737999
-- title:
--   Proposition 4 — a solution of (MVIS) solves (VIP) and (VIS)
-- statement:
--   Let $E,F$ be finite-dimensional real inner product spaces, $U\subseteq E$ a closed convex set, $C\subseteq F$ a closed convex cone with dual cone $C^*$, and let $G:E\to E$, $J:E\to(-\infty,+\infty]$, $\Theta:E\to F$ satisfy the standing assumptions: $G$ is $L$-Lipschitz on $U$, $J$ is proper convex l.s.c., $\Theta$ is $C$-convex and $\tau$-Lipschitz on $U$ ($\tau>0$).
--
--   Let $(u^\natural,p^\natural)$ be a solution of (MVIS). Then
--
--   1. $u^\natural$ solves (VIP);
--   2. $(u^\natural,p^\natural)$ solves (VIS).
--
--   So $\mathbb S_{MVIS}\subseteq\mathbb S_{VIS}$, and Assumption B ($\mathbb S_{MVIS}\neq\emptyset$) implies (H1).
--
--   Differences from the source:
--   - generalization: ℝⁿ and ℝᵐ with the Euclidean inner product → finite-dimensional real inner product spaces E, F; reason: ℝⁿ, ℝᵐ are instances and no coordinate is used, so the statement specializes to the page's
--   - generalization: G continuous on ℝⁿ and L-Lipschitz on U (H2); Θ continuous on ℝⁿ and τ-Lipschitz on an open O ⊇ U (H5) → G L-Lipschitz on U and Θ τ-Lipschitz on U, nothing assumed off U; reason: the proofs evaluate G and Θ only at points of U; the page's hypotheses imply these
--   - reading: J "a continuous function on U" (p.2) and "proper convex l.s.c." (H3, p.4) → J : E → (−∞, +∞] proper, convex, lower semicontinuous (IsProperConvexLSC); reason: the two printed descriptions differ; (H3) is the one the proofs use, and a convex J continuous on the closed set U, extended by +∞, satisfies it
--   - encoding: real values J(u) → (J u).toReal at points of dom J (effDom J); reason: J is finite wherever the statement evaluates it; at points outside dom J the printed inequalities read +∞ ≥ 0
--   - encoding: C a nonempty closed convex cone; C∗ (never defined on the page); Π the projection onto C∗ → C : ProperCone ℝ F; C∗ = ProperCone.innerDual C; Π = CalamaiMore.Convergence.proj onto C∗; reason: every nonempty closed convex cone is a ProperCone; C∗ is used as the dual cone {p | ⟨x, p⟩ ≥ 0 ∀ x ∈ C} (p.7, Example A.4); the projection onto the nonempty closed convex C∗ exists
--   - generalization: Assumption A, including (H1) and (H6) → (H1) and (H6) not assumed; reason: the proof uses neither
-- source:
--   Zhao, Zhu & Zhang, An Augmented Lagrangian Approach to Conically Constrained Non-monotone Variational Inequality Problems, arXiv:2306.01214v1, Proposition 4, p.7 (proof pp.7–8)

import Mathlib
import Definitions.Def_GoldenRatioVI_Fixed_solutionSet
import Definitions.Def_CalamaiMore_Convergence_proj
import Definitions.Def_ALAVI_Standing
import Definitions.Def_ALAVI_IsVIP
import Definitions.Def_ALAVI_IsVIS
import Definitions.Def_ALAVI_IsMVIS

namespace ALAVI

/-- **Proposition 4 (Solution of (MVIS)).** Let `(u♮, p♮)` be a solution of (MVIS). Then
(i) `u♮` solves (VIP); (ii) `(u♮, p♮)` solves (VIS).

Zhao, Zhu & Zhang, arXiv:2306.01214v1, Proposition 4, p.7 (proof pp.7–8).

Formalization Note: under the standing assumptions (closed convex `U`, Lipschitz `G` on `U`,
proper convex l.s.c. `J`, `C`-convex Lipschitz `Θ`); no algorithm and no parameters. `C` is a
closed convex cone (`ProperCone`), which the passage from (21) to `Θ(u♮) ∈ -C` needs. -/
theorem proposition_4 {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (U : Set E) (C : ProperCone ℝ F) (G : E → E) (J : E → EReal) (Θ : E → F) (L τ : ℝ)
    (hA : Standing U C G J Θ L τ) (a : E) (b : F) (h : IsMVIS U C G J Θ a b) :
    IsVIP U C G J Θ a ∧ IsVIS U C G J Θ a b := by sorry

end ALAVI
