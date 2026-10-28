-- Prove2me | Theorems.Thm_CtxInvOpt_PolyCone_lemmaB3_gram_condition
-- name    : CtxInvOpt.PolyCone.lemmaB3_gram_condition
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T08:30:09.590828+00:00
-- url     : https://prove2.me/theorems/29c036e4-322f-4d7e-88c4-3e2c8efac5f3
-- title:
--   Lemma B-3, App-27 — λ_max(G′G)/λ_min(G′G) ≤ (p/φ)² for unit columns with regression residuals ≥ φ
-- statement:
--   Let $p\ge2$ and let $G$ be a matrix of full column rank whose columns $g_1,\dots,g_p\in\mathbb R^m$ have unit norm. For each $i$ let $\Pi_{g_{-i}}$ be the orthogonal projection onto the span of $\{g_1,\dots,g_p\}\setminus\{g_i\}$, and let
--   $$\varphi=\min_{i=1,\dots,p}\ \|g_i-\Pi_{g_{-i}}(g_i)\|$$
--   be the smallest residual of regressing one column on the others. Then the condition number of the Gram matrix satisfies
--   $$\frac{\lambda_{\max}(G'G)}{\lambda_{\min}(G'G)}\ \le\ \Big(\frac{p}{\varphi}\Big)^2 .$$
--
--   The lemma converts a geometric non-collinearity measure of the columns into a spectral one; in the proof of Lemma 10 it feeds the inradius bound of Lemma B-2.
--
--   **Formalization Note** The eigenvalue ratio is stated in its Rayleigh-quotient form: for all $u,v\in\mathbb R^p$, $\|Gu\|^2\|v\|^2\le(p/\varphi)^2\|Gv\|^2\|u\|^2$. This is equivalent, since $\lambda_{\max}$ and $\lambda_{\min}$ are the largest and smallest values of $\|Gu\|^2/\|u\|^2$. The minimum is encoded as any $\varphi>0$ below every residual; the bound is weakest at the minimum itself, so this is equivalent too. **Pinned:** the printed (B-11) takes the minimum over $i=2,\dots,p$ only; with that minimum the bound is false, while the printed proof bounds every diagonal entry of $(G'G)^{-1}$ for $i=1,\dots,p$ and the proof of Lemma 10 applies the lemma with $i=1$ included. The minimum here is over all $i$. Columns lie in $\mathbb R^m$ for any $m$, as the page fixes no row count.
-- source:
--   Besbes, Fonseca, Lobel, Contextual Inverse Optimization: Offline and Online Learning, arXiv:2106.14015v3, p. App-27, Lemma B-3, (B-11); proof App-27–App-28; minimum over all i as in the proof (App-28) and App-20

import Mathlib
import Definitions.Def_CtxInvOpt_PolyCone_Cones

namespace CtxInvOpt.PolyCone

/-- **Lemma B-3 (Condition number of Gram-Matrices), arXiv:2106.14015v3, App-27.** Let `p ≥ 2` and let
`g_0, …, g_{p-1}` be linearly independent unit vectors (the columns of a full-column-rank matrix `G`).
If `0 < φ` and every residual `‖g_i − Π_{g_{−i}}(g_i)‖` (projection on the span of the other vectors)
is at least `φ`, then `λ_max(G′G)/λ_min(G′G) ≤ (p/φ)²`, written in Rayleigh-quotient form:
`‖Gu‖² ‖v‖² ≤ (p/φ)² ‖Gv‖² ‖u‖²` for all `u, v ∈ ℝ^p`.
The page's (B-11) takes the minimum over `i = 2, …, p` only; with that minimum the lemma is false, and
its proof bounds every diagonal entry `a_ii`, `i = 1, …, p`; the minimum here is over all `i`. -/
theorem lemmaB3_gram_condition {m p : ℕ} (hp : 2 ≤ p) (g : Fin p → EuclideanSpace ℝ (Fin m))
    (hli : LinearIndependent ℝ g) (hunit : ∀ i, ‖g i‖ = 1) (φ : ℝ) (hφ : 0 < φ)
    (hφle : ∀ i : Fin p,
      φ ≤ ‖g i - (Submodule.span ℝ (g '' {i}ᶜ)).starProjection (g i)‖) :
    ∀ u v : Fin p → ℝ,
      ‖∑ i, u i • g i‖ ^ 2 * (∑ i, v i ^ 2) ≤
        ((p : ℝ) / φ) ^ 2 * ‖∑ i, v i • g i‖ ^ 2 * (∑ i, u i ^ 2) := by sorry

end CtxInvOpt.PolyCone
