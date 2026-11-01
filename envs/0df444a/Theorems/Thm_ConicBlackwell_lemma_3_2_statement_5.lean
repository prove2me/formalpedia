-- Prove2me | Theorems.Thm_ConicBlackwell_lemma_3_2_statement_5
-- name    : ConicBlackwell.lemma_3_2_statement_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:42:34.620264+00:00
-- url     : https://prove2.me/theorems/93e0951b-05e8-41bf-89e3-0bc9efecd787
-- title:
--   Lemma 3.2, Statement 5 — the order $\le_{\mathcal C^\circ}$: (5) additivity and (6) cancellation
-- statement:
--   Let $\mathcal C\subset\mathbb R^{n+1}$ be a closed convex cone and $\mathcal C^\circ$ its polar, and write $x\le_{\mathcal C^\circ}y$ if and only if $y-x\in\mathcal C^\circ$. Then
--
--   $$
--   x\le_{\mathcal C^\circ}y,\ x'\le_{\mathcal C^\circ}y'\ \Longrightarrow\ x+x'\le_{\mathcal C^\circ}y+y'\qquad\forall x,x',y,y'\in\mathbb R^{n+1},\tag{5}
--   $$
--
--   $$
--   x+x'\le_{\mathcal C^\circ}y\ \Longrightarrow\ x\le_{\mathcal C^\circ}y\qquad\forall x,y\in\mathbb R^{n+1},\ \forall x'\in\mathcal C^\circ.\tag{6}
--   $$
--
--   These two rules let the proof of Theorem 3.3 sum the one-step inequalities (12) and then drop terms lying in $\mathcal C^\circ$.
--
--   Differences from the source:
--   - encoding: ℝⁿ and ℝ × ℝⁿ = ℝⁿ⁺¹ → E n = EuclideanSpace ℝ (Fin n), and lift a x : E (n+1) with the scalar a in coordinate 0; reason: Lean convention of the reused ApproachRegret.ToOLO definitions; same instances (the dimension n = 0 is not excluded; there X ⊆ {0} and the statements stay true)
--   - encoding: closed convex cone C ⊂ ℝⁿ⁺¹ → MoreauProx.Decomposition.IsClosedConvexCone C (nonempty, closed, convex, closed under nonnegative scaling); reason: a cone in the paper contains 0; the nonemptiness clause only excludes the empty set
--   - encoding: x ≤_{C°} y → y - x ∈ polar C; reason: the paper's definition of the order, written out
-- source:
--   Grand-Clément & Kroer, Solving Optimization Problems with Blackwell Approachability, arXiv:2202.12277v1 (https://arxiv.org/abs/2202.12277v1), Lemma 3.2, Statement 5, displays (5)–(6), p.7

import Mathlib
import Definitions.Def_ApproachRegret_ToOLO_Cones
import Definitions.Def_MoreauProx_Decomposition_Cones
open scoped RealInnerProductSpace
open ApproachRegret.ToOLO

namespace ConicBlackwell

/-- **Lemma 3.2, Statement 5**, displays (5)–(6), Grand-Clément & Kroer, arXiv:2202.12277v1, p.7.
Let `C ⊂ ℝⁿ⁺¹` be a closed convex cone and `C°` its polar, and write `x ≤_{C°} y ⟺ y − x ∈ C°`.
Then
(5) `x ≤_{C°} y, x′ ≤_{C°} y′ ⇒ x + x′ ≤_{C°} y + y′` for all `x, x′, y, y′ ∈ ℝⁿ⁺¹`, and
(6) `x + x′ ≤_{C°} y ⇒ x ≤_{C°} y` for all `x, y ∈ ℝⁿ⁺¹` and `x′ ∈ C°`.

Formalization Note: `x ≤_{C°} y` is written out as `y - x ∈ polar C`. -/
theorem lemma_3_2_statement_5 {n : ℕ} (C : Set (E (n + 1)))
    (hC : MoreauProx.Decomposition.IsClosedConvexCone C) :
    (∀ x x' y y' : E (n + 1), y - x ∈ polar C → y' - x' ∈ polar C →
        (y + y') - (x + x') ∈ polar C) ∧
      (∀ x y x' : E (n + 1), x' ∈ polar C → y - (x + x') ∈ polar C → y - x ∈ polar C) := by sorry

end ConicBlackwell
