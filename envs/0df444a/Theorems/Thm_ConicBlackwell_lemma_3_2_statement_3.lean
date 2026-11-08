-- Prove2me | Theorems.Thm_ConicBlackwell_lemma_3_2_statement_3
-- name    : ConicBlackwell.lemma_3_2_statement_3
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T12:42:28.767613+00:00
-- url     : https://prove2.me/theorems/7406869c-014a-4c0d-b7f2-50d037ab45f1
-- title:
--   Lemma 3.2, Statement 3 — $d(u,\mathcal C^\circ)=\|u\|_2$ for $u\in\mathcal C$
-- statement:
--   Let $\mathcal C\subset\mathbb R^{n+1}$ be a closed convex cone and $\mathcal C^\circ$ its polar. If $u\in\mathcal C$, then
--
--   $$
--   d(u,\mathcal C^\circ)=\|u\|_2 ,
--   $$
--
--   where $d(u,S)=\inf_{z\in S}\|u-z\|_2$.
--
--   In the proof of Theorem 3.3 this identifies the distance of the aggregate payoff $u_T\in\mathcal C$ to the target set $\mathcal C^\circ$ with its norm.
--
--   Differences from the source:
--   - encoding: ℝⁿ and ℝ × ℝⁿ = ℝⁿ⁺¹ → E n = EuclideanSpace ℝ (Fin n), and lift a x : E (n+1) with the scalar a in coordinate 0; reason: Lean convention of the reused ApproachRegret.ToOLO definitions; same instances (the dimension n = 0 is not excluded; there X ⊆ {0} and the statements stay true)
--   - encoding: closed convex cone C ⊂ ℝⁿ⁺¹ → MoreauProx.Decomposition.IsClosedConvexCone C (nonempty, closed, convex, closed under nonnegative scaling); reason: a cone in the paper contains 0; the nonemptiness clause only excludes the empty set
--   - encoding: d(u, S) → Metric.infDist u S; reason: the Euclidean distance to a set
-- source:
--   Grand-Clément & Kroer, Solving Optimization Problems with Blackwell Approachability, arXiv:2202.12277v1 (https://arxiv.org/abs/2202.12277v1), Lemma 3.2, Statement 3, p.7

import Mathlib
import Definitions.Def_ApproachRegret_ToOLO_Cones
import Definitions.Def_MoreauProx_Decomposition_Cones
open scoped RealInnerProductSpace
open ApproachRegret.ToOLO

namespace ConicBlackwell

/-- **Lemma 3.2, Statement 3**, Grand-Clément & Kroer, arXiv:2202.12277v1, p.7.
Let `C ⊂ ℝⁿ⁺¹` be a closed convex cone and `C°` its polar.  If `u ∈ C`, then `d(u, C°) = ‖u‖₂`.

Formalization Note: `d(·, ·)` is `Metric.infDist`; `C° = polar C`. -/
theorem lemma_3_2_statement_3 {n : ℕ} (C : Set (E (n + 1)))
    (hC : MoreauProx.Decomposition.IsClosedConvexCone C) (u : E (n + 1)) (hu : u ∈ C) :
    Metric.infDist u (polar C) = ‖u‖ := by sorry

end ConicBlackwell
