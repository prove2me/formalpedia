-- Prove2me | Theorems.Thm_DualTwoStageRO_inf_weighted_sum_eq_neg_inf_perspConj
-- name    : DualTwoStageRO.inf_weighted_sum_eq_neg_inf_perspConj
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:48:37.207794+00:00
-- url     : https://prove2.me/theorems/fcbc3b8b-9527-40cd-a754-bd1545a3f1e4
-- title:
--   Conjugate of a nonnegatively weighted sum through closed perspectives
-- statement:
--   Let $h_0,\dots,h_m:\mathbb R^n\to\mathbb R$ be convex, $v_0,\dots,v_m\ge0$ and $s\in\mathbb R^n$. Then
--
--   $$\inf_{y\in\mathbb R^n}\Bigl\{\sum_{i=0}^mv_ih_i(y)-s^\top y\Bigr\}=-\inf\Bigl\{\sum_{i=0}^mv_i\,h_i^*\Bigl(\frac{u_i}{v_i}\Bigr):\ u_0,\dots,u_m\in\mathbb R^n,\ \sum_{i=0}^mu_i=s\Bigr\}$$
--
--   in the extended reals, where $v_ih_i^*(u_i/v_i)$ is the closed perspective of the conjugate ($0$ if $v_i=0$ and $u_i=0$, $+\infty$ if $v_i=0$ and $u_i\neq0$).
--
--   Equivalently, the conjugate of $\sum_iv_ih_i$ at $s$ is the infimal convolution of the conjugates of the $v_ih_i$, with no closure needed. With $s=-B^\top w$ this turns the Lagrangian of the inner problem of (1) into the constraints $v_i(g_i)^*(u_i/v_i)\le z_i$, $\sum_iu_i=-B^\top w$ of $\mathcal V$.
--
--   **Formalization Note** No attainment is asserted; the right-hand sum is an `EReal` sum of values in $(-\infty,+\infty]$.
--
--   Differences from the source:
--   - generalization: the recourse functions g_0,…,g_{m1} with multipliers v (v_0 = 1) and s = −B⊤w, as in V → arbitrary convex h_0,…,h_m on ℝⁿ, any v ≥ 0 and any s; reason: the paper's use is the instance h = g, m = m1, s = −B⊤w
--   - reading: v_i (g_i)^*(u_i/v_i), with the perspective defined on p.1795 only for real-valued functions → perspConj: v·g^*(u/v) for v > 0; at v = 0, 0 if u = 0 and +∞ otherwise (+∞ for v < 0); reason: Rockafellar's closure (p.67, cited by the page) of the perspective of g^* at v = 0 is the recession function of g^*, the support function of dom g = ℝ^{ny}; the reading 0·(anything) = 0 would enlarge V
--   - encoding: values possibly ±∞ → EReal; reason: Lean convention; same instances
-- source:
--   de Ruiter, Zhen, den Hertog, Technical Note—Dual Approach for Two-Stage Robust Nonlinear Optimization, Operations Research 71(5):1794–1799, 2023, doi:10.1287/opre.2022.2289 (published version, sha256 75cbce38…fe03ac), §1.4, p.1795 (conjugate and perspective); Theorem 1, p.1796 (the set V)

import Mathlib
import Definitions.Def_DualTwoStageRO_perspConj

namespace DualTwoStageRO

/-- **Conjugate of a nonnegatively weighted sum via closed perspectives.**
de Ruiter, Zhen, den Hertog, Operations Research 71(5), 2023: the conjugate `g^*` and the
perspective `t f(ν/t)` (§1.4, p.1795) combine into the constraint `v_i (g_i)^*(u_i/v_i) ≤ z_i`,
`Σ_i u_i = −B⊤w` of the set `V` (Theorem 1, p.1796).

For convex real-valued `h_0,…,h_m` on `ℝⁿ`, weights `v ≥ 0` and `s ∈ ℝⁿ`:
`inf_y [Σ_i v_i h_i(y) − s⊤y] = − inf { Σ_i v_i h_i^*(u_i/v_i) | Σ_i u_i = s }`
in `EReal`, where `v_i h_i^*(u_i/v_i)` is the closed perspective `perspConj` (`0` at `v_i = 0`,
`u_i = 0`; `+∞` at `v_i = 0`, `u_i ≠ 0`).

**Formalization Note.** No attainment is asserted. The sum on the right is an `EReal` sum of values in
`(−∞, +∞]`. -/
theorem inf_weighted_sum_eq_neg_inf_perspConj {n m : ℕ} (h : Fin (m + 1) → (Fin n → ℝ) → ℝ)
    (hh : ∀ i, ConvexOn ℝ Set.univ (h i)) (v : Fin (m + 1) → ℝ) (hv : 0 ≤ v)
    (s : Fin n → ℝ) :
    (⨅ y : Fin n → ℝ, ((∑ i, v i * h i y - s ⬝ᵥ y : ℝ) : EReal)) =
      -⨅ u ∈ {u : Fin (m + 1) → Fin n → ℝ | ∑ i, u i = s}, ∑ i, perspConj (h i) (u i) (v i) := by sorry

end DualTwoStageRO
