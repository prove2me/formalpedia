-- Prove2me | Theorems.Thm_ChanPangGQVI_Existence_lemma_4_1
-- name    : ChanPangGQVI.Existence.lemma_4_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:39:55.63699+00:00
-- url     : https://prove2.me/theorems/fd253a10-07b5-4815-8988-bc002ee473b1
-- title:
--   Lemma 4.1 — strong copositivity at x⁰ implies coercivity at x⁰
-- statement:
--   Let $\mu$ and $K$ be point-to-set mappings of $\mathbb R^n$ into itself. If $\mu$ is strongly copositive with respect to $K$ at a point $x^0$, that is, $x^0\in K(x^0)$ and for some $\alpha>0$ and $y^0\in\mu(x^0)$,
--
--   $$
--   (y-y^0)^T(x-x^0)\ \ge\ \alpha\|x-x^0\|^2\qquad\text{for all } x\in K(x),\ y\in\mu(x),
--   $$
--
--   then $\mu$ is coercive with respect to $K$ at the same point $x^0$:
--
--   $$
--   \lim_{\|x\|\to\infty,\ x\in K(x)}\ \inf_{y\in\mu(x)}\frac{(x-x^0)^T y}{\|x\|}=\infty .
--   $$
--
--   Together with Corollary 4.1 this gives existence for strongly copositive mappings, in particular for strongly monotone ones.
--
--   **Formalization Note** The paper states the lemma without naming the point; its proof establishes condition (4) at the point of strong copositivity, which is the form stated here and the form used in Theorem 4.2.
-- source:
--   Chan and Pang, The generalized quasi-variational inequality problem, Math. Oper. Res. 7 (1982), p. 218, Lemma 4.1

import Mathlib
import Definitions.Def_ChanPangGQVI_Existence_Coercivity

namespace ChanPangGQVI.Existence

/-- Chan and Pang 1982, p. 218, Lemma 4.1. If `μ` is strongly copositive with respect to `K` (at a
point `x⁰`), then it is coercive with respect to `K`. Stated at the same point `x⁰`: condition (4)
holds at `x⁰`, which is what the paper's proof shows and what Theorem 4.2 uses. -/
theorem lemma_4_1 {n : ℕ} (μ K : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n)))
    (x0 : EuclideanSpace ℝ (Fin n)) (h : IsStronglyCopositiveAt μ K x0) :
    IsCoerciveAt μ K x0 := by sorry

end ChanPangGQVI.Existence
