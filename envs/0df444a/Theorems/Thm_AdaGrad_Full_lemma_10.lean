-- Prove2me | Theorems.Thm_AdaGrad_Full_lemma_10
-- name    : AdaGrad.Full.lemma_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:45:47.415838+00:00
-- url     : https://prove2.me/theorems/54343851-37c8-4184-b76b-ea63077ad14f
-- title:
--   Lemma 10 — $\sum_t\langle g_t,S_t^\dagger g_t\rangle\le2\sum_t\langle g_t,S_T^\dagger g_t\rangle=2\operatorname{tr}(G_T^{1/2})$
-- statement:
--   Let $g_1,g_2,\dots\in\mathbb R^d$, $G_t=\sum_{\tau=1}^t g_\tau g_\tau^\top$, $S_t=G_t^{1/2}$ as in Figure 2, and let $A^\dagger$ denote the pseudo-inverse of $A$. Then for every $T$,
--   $$\sum_{t=1}^T\big\langle g_t,S_t^\dagger g_t\big\rangle\le2\sum_{t=1}^T\big\langle g_t,S_T^\dagger g_t\big\rangle=2\operatorname{tr}(G_T^{1/2}).$$
--
--   This is the full-matrix doubling lemma: the adaptive dual norms sum to at most twice the trace of the final root, which is what makes $\operatorname{tr}(G_T^{1/2})$ appear in Theorem 7.
--
--   **Formalization Note** $S_t^\dagger$ is the functional-calculus pseudo-inverse of $S_t$ (zero on the kernel), not Mathlib's matrix inverse, which would vanish on every singular $S_t$ and make the equality false.
-- source:
--   Duchi, Hazan, Singer, Adaptive Subgradient Methods for Online Learning and Stochastic Optimization, JMLR 12 (2011), p. 2135, Lemma 10

import Mathlib
import Definitions.Def_AdaGrad_Full_Algorithm2
open scoped MatrixOrder InnerProductSpace

namespace AdaGrad.Full

/-- Lemma 10 (p. 2135): with `S_t = G_t^{1/2}` and `†` the pseudo-inverse,
`∑_{t=1}^T ⟨g_t, S_t† g_t⟩ ≤ 2 ∑_{t=1}^T ⟨g_t, S_T† g_t⟩ = 2 tr(G_T^{1/2})`. -/
theorem lemma_10 {d : ℕ} (g : ℕ → EuclideanSpace ℝ (Fin d)) (T : ℕ) :
    ∑ t ∈ Finset.Icc 1 T, mInner (pinv (S g t)) (g t) (g t)
        ≤ 2 * ∑ t ∈ Finset.Icc 1 T, mInner (pinv (S g T)) (g t) (g t) ∧
      2 * ∑ t ∈ Finset.Icc 1 T, mInner (pinv (S g T)) (g t) (g t) = 2 * (S g T).trace := by sorry

end AdaGrad.Full
