-- Prove2me | Theorems.Thm_ChanPangGQVI_Contraction_theorem_5_1
-- name    : ChanPangGQVI.Contraction.theorem_5_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:02:57.433538+00:00
-- url     : https://prove2.me/theorems/7f39b51d-1716-494b-aab8-9928d19cfb2c
-- title:
--   Theorem 5.1 — solutions of GQVI(K, f) are the fixed points $x^*=P_{K(x^*)}(x^*-y^*)$, $y^*\in f(x^*)$
-- statement:
--   Let $f$ and $K$ be point-to-set mappings of $\mathbb R^n$ into itself such that $K(x)$ is a closed convex set for every $x$. For a set $S$ and a point $z$ write $P_S(z)$ for the projection of $z$ on $S$, the nearest point of $S$ to $z$ in the Euclidean norm. Then a pair $(x^*,y^*)$ solves the generalized quasi-variational inequality $\mathrm{GQVI}(K,f)$ if and only if
--
--   $$
--   x^*=P_{K(x^*)}(x^*-y^*)\qquad\text{and}\qquad y^*\in f(x^*).
--   $$
--
--   The theorem turns the GQVI into a fixed-point problem for a projection map. In this mission it is applied with $\lambda f$ in place of $f$ to read the fixed point of $F_\lambda(x)=P_{K(x)}(x-\lambda f(x))$ as a solution of the GQVI.
--
--   **Formalization Note** The equation $x^*=P_{K(x^*)}(x^*-y^*)$ is stated relationally: $x^*\in K(x^*)$ and $\|x^*-(x^*-y^*)\|\le\|q-(x^*-y^*)\|$ for every $q\in K(x^*)$. For a closed convex set the nearest point is unique, so this is the paper's equation, and no junk value of a projection function is involved when $K(x^*)$ is empty.
-- source:
--   Chan and Pang, The generalized quasi-variational inequality problem, Math. Oper. Res. 7 (1982), p. 220, Theorem 5.1

import Mathlib
import Definitions.Def_ChanPangGQVI_Shared_GQVI
import Definitions.Def_ChanPangGQVI_Shared_Projection

open scoped RealInnerProductSpace

namespace ChanPangGQVI.Contraction

/-- **Theorem 5.1** (Chan and Pang 1982, p. 220). Let `f` and `K` be point-to-set mappings of
`ℝⁿ` into itself with `K(x)` closed and convex for all `x`. Then `(x*, y*)` solves `GQVI(K, f)`
if and only if `x* = P_{K(x*)}(x* - y*)` and `y* ∈ f(x*)`.

The equation `x* = P_{K(x*)}(x* - y*)` is written relationally, `IsProj (K x*) (x* - y*) x*`
("`x*` is a nearest point of `K(x*)` to `x* - y*`"), so that no junk value of a projection
function enters when `K(x*)` is empty; for a closed convex set the nearest point is unique, so
this is the paper's equation. -/
theorem theorem_5_1 {n : ℕ}
    (K f : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n)))
    (hK_closed : ∀ x, IsClosed (K x)) (hK_convex : ∀ x, Convex ℝ (K x))
    (xs ys : EuclideanSpace ℝ (Fin n)) :
    ChanPangGQVI.Shared.IsGQVISolution K f xs ys ↔
      (ChanPangGQVI.Shared.IsProj (K xs) (xs - ys) xs ∧ ys ∈ f xs) := by sorry

end ChanPangGQVI.Contraction
