-- Prove2me | Theorems.Thm_ChanPangGQVI_Existence_proposition_2_1
-- name    : ChanPangGQVI.Existence.proposition_2_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:40:42.184533+00:00
-- url     : https://prove2.me/theorems/f9c92a2a-285e-45fc-9169-09bf053d6d75
-- title:
--   Proposition 2.1 — GICP(L, m, f) and GQVI(K, f) with K = m + L have the same solutions
-- statement:
--   Let $m$ be a point-to-point mapping and $f$ a point-to-set mapping of $\mathbb R^n$ into itself, and let $L$ be a cone-valued mapping on $\mathbb R^n$ (each $L(x)$ a convex cone containing the origin). Define $K(x)=m(x)+L(x)$ as in equation (1). Then a pair $(x,y)$ solves the generalized implicit complementarity problem $\mathrm{GICP}(L,m,f)$,
--
--   $$
--   x\in m(x)+L(x),\qquad y\in f(x)\cap L(x)^*,\qquad y^T(x-m(x))=0,
--   $$
--
--   if and only if it solves the generalized quasi-variational inequality $\mathrm{GQVI}(K,f)$,
--
--   $$
--   x\in K(x),\qquad y\in f(x),\qquad (x'-x)^T y\ge 0\ \text{ for all } x'\in K(x).
--   $$
--
--   That is, the solution sets of the two problems are equal. The proposition extends earlier results of Karamardian, Fang and Pang, and it is how the existence theorems for the GQVI yield existence for the GICP.
-- source:
--   Chan and Pang, The generalized quasi-variational inequality problem, Math. Oper. Res. 7 (1982), p. 213, Proposition 2.1

import Mathlib
import Definitions.Def_ChanPangGQVI_Existence_GQVI
import Definitions.Def_ChanPangGQVI_Existence_GICP

namespace ChanPangGQVI.Existence

/-- Chan and Pang 1982, p. 213, Proposition 2.1. For a point-to-point mapping `m`, a cone-valued
mapping `L` and a point-to-set mapping `f` of `ℝⁿ`, the solution sets of `GICP(L, m, f)` and
`GQVI(K, f)` with `K(x) = m(x) + L(x)` (equation (1)) are equal: a pair `(x, y)` solves one problem
if and only if it solves the other. -/
theorem proposition_2_1 {n : ℕ}
    (L : EuclideanSpace ℝ (Fin n) → PointedCone ℝ (EuclideanSpace ℝ (Fin n)))
    (m : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (f : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n))) :
    ∀ x y : EuclideanSpace ℝ (Fin n),
      IsGICPSolution L m f x y ↔ IsGQVISolution (coneTranslate m L) f x y := by sorry

end ChanPangGQVI.Existence
