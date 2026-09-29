-- Prove2me | Theorems.Thm_ChanPangGQVI_ProjExistence_theorem_5_1
-- name    : ChanPangGQVI.ProjExistence.theorem_5_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:42:38.178148+00:00
-- url     : https://prove2.me/theorems/91c8020c-cd5a-4851-bc0c-c68dcdb69e3c
-- title:
--   Theorem 5.1 — (x*, y*) solves GQVI(K, f) iff x* = P_{K(x*)}(x* − y*) and y* ∈ f(x*)
-- statement:
--   Let $K$ and $f$ be point-to-set mappings of $\mathbb R^n$ into itself, and suppose that $K(x)$ is closed and convex for every $x$. For $u,z\in\mathbb R^n$ let $P_{K(u)}(z)$ denote the projection of $z$ on $K(u)$, the nearest point of $K(u)$ to $z$ in the Euclidean norm. Then for every pair $(x^*,y^*)$,
--
--   $$
--   (x^*,y^*)\ \text{solves}\ \mathrm{GQVI}(K,f)\quad\Longleftrightarrow\quad x^*=P_{K(x^*)}(x^*-y^*)\ \text{ and }\ y^*\in f(x^*).
--   $$
--
--   The theorem characterizes the solutions of the GQVI as the fixed points of the composite map $x\mapsto P_{K(x)}(x-y)$, $y\in f(x)$. It is the bridge by which fixed-point theorems (Brouwer, contraction mappings) yield existence and computation results for the GQVI.
--
--   **Formalization Note** The equation $x^*=P_{K(x^*)}(x^*-y^*)$ is written relationally: $x^*\in K(x^*)$ and $\|x^*-(x^*-y^*)\|\le\|q-(x^*-y^*)\|$ for all $q\in K(x^*)$. For a closed convex set the nearest point is unique, so this is the paper's equation; the relational form keeps a junk value of a projection function out of the statement when $K(x^*)$ is empty. The equivalence is stated for every pair $(x^*,y^*)$.
-- source:
--   Chan and Pang, The generalized quasi-variational inequality problem, Math. Oper. Res. 7 (1982), p. 220, Theorem 5.1

import Mathlib
import Definitions.Def_ChanPangGQVI_Shared_GQVI
import Definitions.Def_ChanPangGQVI_Shared_Projection

open scoped RealInnerProductSpace

namespace ChanPangGQVI.ProjExistence

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

end ChanPangGQVI.ProjExistence
