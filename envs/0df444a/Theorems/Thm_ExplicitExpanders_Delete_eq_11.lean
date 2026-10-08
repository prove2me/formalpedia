-- Prove2me | Theorems.Thm_ExplicitExpanders_Delete_eq_11
-- name    : ExplicitExpanders.Delete.eq_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T07:16:19.585346+00:00
-- url     : https://prove2.me/theorems/418f81c5-ddac-4435-96f6-3c1b81d7f88b
-- title:
--   Inequality (11) — the matched vertices carry at most a $1/r$ fraction of an eigenvector's mass
-- statement:
--   Let $H$ be a finite $d$-regular graph on $V$ with $d\ge 3$, let $r\ge 1$, and let $U\subseteq V$ satisfy the conclusions 2 and 3 of Lemma 3.1 (the $(r+1)$-neighbourhood of each vertex of $U$ contains no cycle; distinct vertices of $U$ are at distance at least $2r+3$). Let $m$ be a perfect matching on $N(U)$ and $G = H'\cup M$ the resulting graph. If $f$ is an eigenvector of $A_G$ with eigenvalue $\mu$, $|\mu| \ge 2\sqrt{d-1}$, then
--   $$\sum_{uv\in M} \bigl(f^2(u)+f^2(v)\bigr) \le \frac1r \sum_{w} f^2(w). \tag{11}$$
--
--   In the paper $r = \lceil 2/\varepsilon\rceil$ and $\sum_w f^2(w) = 1$, so the right side is at most $\varepsilon/2$, which is the last inequality of (11). The paper assumes $\mu\ge 2\sqrt{d-1}$ ("we thus assume that $\lambda \ge 2\sqrt{d-1}$"); the case $\mu\le-2\sqrt{d-1}$ is needed as well and is included here.
--
--   **Formalization Note** The left-hand side is written as $\sum_x \deg_M(x) f(x)^2$, as in (10). The paper cites "Lemma 2.2" here, a typo for Lemma 3.2.
-- source:
--   N. Alon, Explicit expanders of every degree and size, arXiv:2003.11673v1, p. 13, inequality (11)

import Mathlib
import Definitions.Def_ExplicitExpanders_Delete_IsNDLambda
import Definitions.Def_ExplicitExpanders_Delete_Neighbourhoods
import Definitions.Def_ExplicitExpanders_Delete_DeleteAndMatch

namespace ExplicitExpanders.Delete

open Matrix

open Classical in
/-- (11) (Alon, arXiv:2003.11673v1, p. 13): for an eigenvector `f` of `G = H' + M` with eigenvalue
`|μ| ≥ 2√(d-1)`, `∑_{uv ∈ M} (f(u)² + f(v)²) ≤ (1/r) ∑_w f(w)²`; the left side is written as
`∑_x deg_M(x) f(x)²`. -/
theorem eq_11 {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (d r : ℕ) (hd : 3 ≤ d) (hreg : H.IsRegularOfDegree d) (hr : 1 ≤ r)
    (U : Finset V) (hU2 : ∀ z ∈ U, NoCycleOn H (ball H z (r + 1)))
    (hU3 : ∀ z ∈ U, ∀ z' ∈ U, z ≠ z' → ((2 * r + 3 : ℕ) : ℕ∞) ≤ H.edist z z')
    (m : V → V) (hm : IsMatchingOn (nbrSet H U) m)
    (f : Kept U → ℝ) (μ : ℝ) (heig : (deleteAndMatch H U m).adjMatrix ℝ *ᵥ f = μ • f)
    (hμ : 2 * Real.sqrt ((d : ℝ) - 1) ≤ |μ|) :
    ∑ x, ((matchGraph H U m).degree x : ℝ) * f x ^ 2 ≤ (1 / (r : ℝ)) * ∑ x, f x ^ 2 := by sorry

end ExplicitExpanders.Delete
