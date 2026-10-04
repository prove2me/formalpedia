-- Prove2me | Theorems.Thm_BarvinokCount_ShortFormula_exists_moment_vector_not_orthogonal
-- name    : BarvinokCount.ShortFormula.exists_moment_vector_not_orthogonal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T05:32:04.590899+00:00
-- url     : https://prove2.me/theorems/ccc7278e-9902-437f-9047-ac663e5d3662
-- title:
--   Lemma 6.1 — some c(t) = (1, t, …, t^{d−1}) with t ∈ {0, 1, …, m(d−1)} is orthogonal to none of u_1, …, u_m
-- statement:
--   Let $d,m\in\mathbb{N}$ and let $u_1,\dots,u_m\in\mathbb{Q}^d$ be nonzero rational vectors. Then there is $t\in\{0,1,\dots,m\cdot(d-1)\}$ such that the rational vector
--   $$c(t)=(1,t,\dots,t^{d-1})$$
--   satisfies
--   $$\langle c(t),u_i\rangle\ne0\qquad(i=1,\dots,m).$$
--
--   In the algorithm this produces the generic direction $c$ that is regular for all the primitive cones of the decomposition.
--
--   **Formalization Note** The printed lemma asserts a polynomial time algorithm constructing some $c\in\mathbb{Q}^d$ with $\langle c,u_i\rangle\ne0$; its proof searches $c(t)$ over $t\in\{0,1,\dots,m(d-1)\}$. That explicit form, which contains the printed conclusion, is stated here in place of the algorithmic clause. The hypothesis $u_i\ne0$ is added: the printed statement omits it, the proof uses it ("nonzero polynomials"), and for $u_i=0$ the claim is false. The convention $0^0=1$ gives $c(0)=(1,0,\dots,0)$.
-- source:
--   Barvinok, A polynomial time algorithm for counting integral points in polyhedra when the dimension is fixed, Math. Oper. Res. 19 (1994), pp. 777–778, Lemma 6.1 and its proof

import Mathlib

namespace BarvinokCount.ShortFormula

theorem exists_moment_vector_not_orthogonal (d m : ℕ) (u : Fin m → Fin d → ℚ)
    (hu : ∀ i, u i ≠ 0) :
    ∃ t ∈ Finset.range (m * (d - 1) + 1),
      ∀ i, (fun l : Fin d => (t : ℚ) ^ (l : ℕ)) ⬝ᵥ u i ≠ 0 := by sorry

end BarvinokCount.ShortFormula
