-- Prove2me | Theorems.Thm_ExplicitExpanders_Delete_eq_10
-- name    : ExplicitExpanders.Delete.eq_10
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T07:16:13.32098+00:00
-- url     : https://prove2.me/theorems/a15c670b-b0d7-4b18-beaf-914abcd227e3
-- title:
--   Inequality (10) — $|f^tA_Mf| \le \sum_{uv\in M} f^2(u)+f^2(v)$
-- statement:
--   Let $H$ be a finite graph on $V$, $U\subseteq V$, $m$ a perfect matching on $N(U)$, and $M$ the matching graph on $V\setminus U$ with adjacency matrix $A_M$. For every $f : V\setminus U\to\mathbb R$,
--   $$|f^{t}A_M f| = \Bigl|2\sum_{uv\in M} f(u)f(v)\Bigr| \le \sum_{uv\in M} \bigl(f^2(u)+f^2(v)\bigr). \tag{10}$$
--
--   The right-hand side is written vertex by vertex: each vertex $x$ appears in $\deg_M(x)\in\{0,1\}$ edges of $M$, so $\sum_{uv\in M}(f^2(u)+f^2(v)) = \sum_x \deg_M(x)\, f(x)^2$. Together with (11) this bounds the contribution of the added matching to the Rayleigh quotient of $G$.
--
--   **Formalization Note** The conclusion is $|f \cdot A_M f| \le \sum_x \deg_M(x) f(x)^2$.
-- source:
--   N. Alon, Explicit expanders of every degree and size, arXiv:2003.11673v1, p. 13, inequality (10)

import Mathlib
import Definitions.Def_ExplicitExpanders_Delete_IsNDLambda
import Definitions.Def_ExplicitExpanders_Delete_Neighbourhoods
import Definitions.Def_ExplicitExpanders_Delete_DeleteAndMatch

namespace ExplicitExpanders.Delete

open Matrix

open Classical in
/-- (10) (Alon, arXiv:2003.11673v1, p. 13): `|fᵗ A_M f| ≤ ∑_{uv ∈ M} (f(u)² + f(v)²)`. The right
side is written vertex by vertex: `∑_{uv ∈ M} (f(u)² + f(v)²) = ∑_x deg_M(x) f(x)²`. -/
theorem eq_10 {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (U : Finset V) (m : V → V) (hm : IsMatchingOn (nbrSet H U) m) (f : Kept U → ℝ) :
    |f ⬝ᵥ ((matchGraph H U m).adjMatrix ℝ *ᵥ f)| ≤
      ∑ x, ((matchGraph H U m).degree x : ℝ) * f x ^ 2 := by sorry

end ExplicitExpanders.Delete
