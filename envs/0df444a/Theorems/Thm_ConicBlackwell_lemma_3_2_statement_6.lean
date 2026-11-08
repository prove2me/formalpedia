-- Prove2me | Theorems.Thm_ConicBlackwell_lemma_3_2_statement_6
-- name    : ConicBlackwell.lemma_3_2_statement_6
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T12:42:35.094054+00:00
-- url     : https://prove2.me/theorems/25cbda86-c8a7-4ce8-acbb-f40300f2303a
-- title:
--   Lemma 3.2, Statement 6 — $x\le_{\mathcal C^\circ}y\Rightarrow d(y,\mathcal C^\circ)\le\|x\|_2$
-- statement:
--   Let $\mathcal C\subset\mathbb R^{n+1}$ be a closed convex cone and $\mathcal C^\circ$ its polar, with $x\le_{\mathcal C^\circ}y$ meaning $y-x\in\mathcal C^\circ$. If $x\le_{\mathcal C^\circ}y$ for $x,y\in\mathbb R^{n+1}$, then
--
--   $$
--   d(y,\mathcal C^\circ)\le\|x\|_2 .
--   $$
--
--   This converts the order inequality between the weighted payoff sum and $(\theta_T/\omega_T)u_T$ into the distance bound (13).
--
--   Differences from the source:
--   - encoding: ℝⁿ and ℝ × ℝⁿ = ℝⁿ⁺¹ → E n = EuclideanSpace ℝ (Fin n), and lift a x : E (n+1) with the scalar a in coordinate 0; reason: Lean convention of the reused ApproachRegret.ToOLO definitions; same instances (the dimension n = 0 is not excluded; there X ⊆ {0} and the statements stay true)
--   - encoding: closed convex cone C ⊂ ℝⁿ⁺¹ → MoreauProx.Decomposition.IsClosedConvexCone C (nonempty, closed, convex, closed under nonnegative scaling); reason: a cone in the paper contains 0; the nonemptiness clause only excludes the empty set
--   - encoding: x ≤_{C°} y → y - x ∈ polar C; reason: the paper's definition of the order, written out
--   - encoding: d(u, S) → Metric.infDist u S; reason: the Euclidean distance to a set
-- source:
--   Grand-Clément & Kroer, Solving Optimization Problems with Blackwell Approachability, arXiv:2202.12277v1 (https://arxiv.org/abs/2202.12277v1), Lemma 3.2, Statement 6, p.7

import Mathlib
import Definitions.Def_ApproachRegret_ToOLO_Cones
import Definitions.Def_MoreauProx_Decomposition_Cones
open scoped RealInnerProductSpace
open ApproachRegret.ToOLO

namespace ConicBlackwell

/-- **Lemma 3.2, Statement 6**, Grand-Clément & Kroer, arXiv:2202.12277v1, p.7.
Let `C ⊂ ℝⁿ⁺¹` be a closed convex cone and `C°` its polar.  Assume that `x ≤_{C°} y` for
`x, y ∈ ℝⁿ⁺¹`.  Then `d(y, C°) ≤ ‖x‖₂`.

Formalization Note: `x ≤_{C°} y` is `y - x ∈ polar C`; `d` is `Metric.infDist`. -/
theorem lemma_3_2_statement_6 {n : ℕ} (C : Set (E (n + 1)))
    (hC : MoreauProx.Decomposition.IsClosedConvexCone C) (x y : E (n + 1))
    (hxy : y - x ∈ polar C) :
    Metric.infDist y (polar C) ≤ ‖x‖ := by sorry

end ConicBlackwell
