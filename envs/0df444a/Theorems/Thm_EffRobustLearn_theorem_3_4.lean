-- Prove2me | Theorems.Thm_EffRobustLearn_theorem_3_4
-- name    : EffRobustLearn.theorem_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:35:51.354473+00:00
-- url     : https://prove2.me/theorems/1e8becd8-f3a4-4b55-b6c8-cfa2bfe64325
-- title:
--   Theorem 3.4 — online Frank–Wolfe with an approximate linear oracle, regret $9D_2G_2T^{3/4}$
-- statement:
--   Let $K$ be a compact convex set of diameter at most $D_2>0$, let $T\in\mathbb N$, and let $(g_t)_{t=1}^T$ satisfy $\|g_t\|_2\le G_2$ with $G_2>0$. Fix $u_1\in K$, set $\alpha=D_2/(2G_2T^{3/4})$ and $\gamma_t=\min(1,2/\sqrt t)$. Let $F_t(u)=\alpha\sum_{r=1}^{t-1}\langle g_r,u\rangle-\|u-u_1\|_2^2$. If $v_t\in K$ satisfies
--   $$\langle\nabla F_t(u_t),v_t\rangle\ge\max_{v\in K}\langle\nabla F_t(u_t),v\rangle-\frac{D_2^2\gamma_t}{100}$$
--   and $u_{t+1}=(1-\gamma_t)u_t+\gamma_tv_t$, then for every $u\in K$,
--   $$\sum_{t=1}^T\langle u,g_t\rangle\le\sum_{t=1}^T\langle u_t,g_t\rangle+9D_2G_2T^{3/4}.$$
--
--   **Formalization Note** The sequences are arbitrary functions quantified together, which covers adaptive $g_t$.
--
--   Differences from the source:
--   - generalization: Euclidean $K$ → $K$ in any real inner product space; reason: the proof uses only inner products and compactness; Euclidean space is the instance
--   - encoding: $\nabla F_t(u_t)$; $\max_{v\in K}$ → the gradient written out as $\alpha\sum_{r<t}g_r-2(u_t-u_1)$; a bound against every $v\in K$; reason: $F_t$ is explicit and $K$ is compact, so the maximum is attained
-- source:
--   Klivans, Stavropoulos, Tikhonov, Vasilyan, Efficient Robust Learning at the Information-Theoretic Limit, arXiv:2609.17655 (held version, sha256 312a0857…), Theorem 3.4, pp.14–15 (PDF pp.15–16)

import Mathlib
import Definitions.Def_EffRobustLearn_numRounds

namespace EffRobustLearn

/-- Theorem 3.4 (Online Frank–Wolfe, adapted from [Haz22, Theorem 7.3]), pp.14–15 (arXiv:2609.17655, held version, sha256 312a0857…). The objective is
`F_t(u) = α ∑_{r<t} ⟨g_r, u⟩ - ‖u - u_1‖²`, whose gradient `α ∑_{r<t} g_r - 2(u - u_1)` is written out; line (3.3) is stated as a bound against
every `v ∈ K`, equivalent to the `max` since `K` is compact and nonempty. Rounds are 1-based.

**Formalization Note.** A fixed function `g` quantified with `u` and `v` covers adaptive sequences `g_t`. Related: the published
`OnlineConvexOpt.ProjectionFree.ocg_regret_v2` is the exact-oracle version, with constant 8; it does not imply this approximate-oracle statement. -/
theorem theorem_3_4 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : Set E) (hKc : IsCompact K) (hKv : Convex ℝ K) (D₂ G₂ : ℝ) (hD : 0 < D₂) (hG : 0 < G₂)
    (hdiam : ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ D₂) (T : ℕ)
    (g u v : ℕ → E) (hg : ∀ t ∈ Finset.Icc 1 T, ‖g t‖ ≤ G₂) (hu1 : u 1 ∈ K)
    (α : ℝ) (hα : α = D₂ / (2 * G₂ * (T : ℝ) ^ (3 / 4 : ℝ)))
    (hv : ∀ t ∈ Finset.Icc 1 T, v t ∈ K ∧ ∀ w ∈ K,
      inner ℝ (α • ∑ r ∈ Finset.Ico 1 t, g r - (2 : ℝ) • (u t - u 1)) w - D₂ ^ 2 * stepSize t / 100 ≤
        inner ℝ (α • ∑ r ∈ Finset.Ico 1 t, g r - (2 : ℝ) • (u t - u 1)) (v t))
    (hstep : ∀ t ∈ Finset.Icc 1 T, u (t + 1) = (1 - stepSize t) • u t + stepSize t • v t) :
    ∀ w ∈ K, ∑ t ∈ Finset.Icc 1 T, inner ℝ w (g t) ≤
      ∑ t ∈ Finset.Icc 1 T, inner ℝ (u t) (g t) + 9 * D₂ * G₂ * (T : ℝ) ^ (3 / 4 : ℝ) := by sorry

end EffRobustLearn
