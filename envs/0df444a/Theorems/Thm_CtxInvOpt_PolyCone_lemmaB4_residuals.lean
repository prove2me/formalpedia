-- Prove2me | Theorems.Thm_CtxInvOpt_PolyCone_lemmaB4_residuals
-- name    : CtxInvOpt.PolyCone.lemmaB4_residuals
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:30:04.71949+00:00
-- url     : https://prove2.me/theorems/1c8ee1b7-a41d-4129-a819-5562e059d10b
-- title:
--   Lemma B-4, App-28 — sequentially η-separated unit vectors have residual ≥ η^{2(p−i)}(η²)^{1{i>1}} against all others
-- statement:
--   Let $g_1,\dots,g_p\in\mathbb R^m$ be unit vectors and $\eta\in\mathbb R$. For a set $S$ of vectors write $\Pi_S$ for the orthogonal projection onto the subspace spanned by $S$, and $g_{-i}=\{g_j: j\ne i\}$. Suppose every vector after the first is far from the span of its predecessors,
--   $$\|g_i-\Pi_{g_1,\dots,g_{i-1}}(g_i)\|^2\ \ge\ \eta^2,\qquad i=2,\dots,p. \tag{B-14}$$
--   Then for every $i=1,\dots,p$,
--   $$\|g_i-\Pi_{g_{-i}}(g_i)\|^2\ \ge\ \eta^{2(p-i)}\,(\eta^2)^{\mathbf 1\{i>1\}}. \tag{B-15}$$
--
--   A separation condition that only looks backwards (each vector against the earlier ones) thus yields a two-sided one (each vector against all the others), at the price of a factor $\eta^2$ per later vector. In the proof of Lemma 10 it bounds the smallest regression residual of the generators from below.
--
--   **Formalization Note** Vectors are indexed by `Fin p`, so Lean's index $i$ is the paper's $i+1$: the bound reads $\eta^{2(p-1-i)}$ times $1$ if $i=0$ and $\eta^2$ otherwise. The page places the vectors in $\mathbb R^p$; the statement is posed in $\mathbb R^m$ for every $m$, which is equivalent, since $p$ vectors span a subspace isometric to a subspace of $\mathbb R^p$. The page gives no range for $\eta$; none is assumed, as only $\eta^2$ and even powers of $\eta$ occur. The projection is Mathlib's `Submodule.starProjection` onto `Submodule.span`.
-- source:
--   Besbes, Fonseca, Lobel, Contextual Inverse Optimization: Offline and Online Learning, arXiv:2106.14015v3, p. App-28, Lemma B-4, (B-14), (B-15); proof App-28–App-29

import Mathlib
import Definitions.Def_CtxInvOpt_PolyCone_Cones

namespace CtxInvOpt.PolyCone

/-- **Lemma B-4 (Residuals), arXiv:2106.14015v3, App-28.** Let `g_0, …, g_{p-1}` be unit vectors such
that each `g_i` with `i ≥ 1` has squared residual at least `η²` after projection on
`span{g_0, …, g_{i-1}}` (B-14). Then the squared residual of `g_i` after projection on the span of all
the other vectors is at least `η^{2(p-1-i)} (η²)^{1{i ≥ 1}}` (B-15). Indices are 0-based: Lean's `i` is
the paper's `i + 1`. -/
theorem lemmaB4_residuals {m p : ℕ} (η : ℝ) (g : Fin p → EuclideanSpace ℝ (Fin m))
    (hunit : ∀ i, ‖g i‖ = 1)
    (hsep : ∀ i : Fin p, 0 < i.val →
      η ^ 2 ≤ ‖g i - (Submodule.span ℝ (g '' {j | j < i})).starProjection (g i)‖ ^ 2) :
    ∀ i : Fin p, η ^ (2 * (p - 1 - i.val)) * (if i.val = 0 then 1 else η ^ 2) ≤
      ‖g i - (Submodule.span ℝ (g '' {i}ᶜ)).starProjection (g i)‖ ^ 2 := by sorry

end CtxInvOpt.PolyCone
