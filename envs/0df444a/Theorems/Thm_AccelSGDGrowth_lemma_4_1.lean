-- Prove2me | Theorems.Thm_AccelSGDGrowth_lemma_4_1
-- name    : AccelSGDGrowth.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:32:59.729675+00:00
-- url     : https://prove2.me/theorems/229df367-fd5e-41ce-9bd0-e8ebad192b7d
-- title:
--   Lemma 4.1 — the dual-averaging minimizer and the lower bound $f(x_\star)\ge L_{k+1}$
-- statement:
--   Let $m>0$, $k\ge1$, positive weights $a_1,\dots,a_k$, iterates $x_1,\dots,x_k$ and arbitrary vectors $g_1,\dots,g_k$ in $\mathbb R^d$. With (4.2), set $z_{k+1}=-\sum_{i=1}^k a_ig_i$ and
--   $$
--   h_k(x)=\sum_{i=1}^k a_ig_i^\top(x-x_i)+\phi_k(x).
--   $$
--   Then:
--
--   1. $\nabla\phi_k^\star(z_{k+1})=\arg\min_xh_k(x)$: it minimizes $h_k$, and it is the only minimizer;
--   2. $h_k(\nabla\phi_k^\star(z_{k+1}))=-\phi_k^\star(z_{k+1})-\sum_{i=1}^k a_ig_i^\top x_i$;
--   3. if $f\in\mathcal F(m,\mathcal L)$ with $m\le\mathcal L$ and $x_\star$ minimizes $f$, then $f(x_\star)\ge L_{k+1}$, with $L_{k+1}$ of (4.3) and $\varepsilon_i=g_i-\nabla f(x_i)$.
--
--   This is the "lower bound" step of the duality-gap analysis: $L_{k+1}$ is a computable lower bound on the optimal value.
--
--   Differences from the source:
--   - reading: Lemma 4.1(c) stated without naming f's class → f ∈ F(m, L) with 0 < m ≤ L in clause (c); reason: f ∈ F(m, L) is the paper's standing assumption (§2, p.5); the proof uses its strong convexity (4.4)
--   - encoding: arg min_x h_k(x) → IsMinOn h_k univ at ∇φ⋆_k(z_{k+1}) and every minimizer equals it; reason: the argmin of a strongly convex quadratic is a unique point
-- source:
--   Chen, Na, Kolar, Convergence Analysis of Accelerated Stochastic Gradient Descent under the Growth Condition, arXiv:2006.06782v4 (preprint basis), https://arxiv.org/abs/2006.06782v4, Lemma 4.1, pp.14–15, with (4.2) and (4.3)

import Definitions.Def_AccelSGDGrowth_ClassF
import Definitions.Def_AccelSGDGrowth_lowerL

namespace AccelSGDGrowth

/-- Chen, Na, Kolar, arXiv:2006.06782v4, Lemma 4.1, pp.14–15. Let `m > 0`, `k ≥ 1`, positive weights
`a_1, …, a_k`, iterates `x_1, …, x_k` and arbitrary vectors `g_1, …, g_k`. With (4.2):
`A_k = Σ a_i`, `z_{k+1} = −Σ_{i=1}^k a_i g_i`, `φ_k(x) = Σ (a_i m/2)‖x − x_i‖²`,
`h_k(x) = Σ_{i=1}^k a_i g_iᵀ(x − x_i) + φ_k(x)`:
(a) `∇φ⋆_k(z_{k+1}) = argmin_x h_k(x)` (it minimizes `h_k`, and is the only minimizer);
(b) `h_k(∇φ⋆_k(z_{k+1})) = −φ⋆_k(z_{k+1}) − Σ a_i g_iᵀ x_i`;
(c) for `f ∈ F(m, L)` with minimizer `x⋆`, `f(x⋆) ≥ L_{k+1}`, with `L_{k+1}` of (4.3) and
    `ε_i = g_i − ∇f(x_i)`.

**Formalization Note.** Deterministic (pointwise in the outcome). `L_{k+1}` is `lowerL … (k+1)`,
which builds `z_{k+1}` from the same sum. In (c) the paper's standing assumption `f ∈ F(m, L)`
(§2, p.5) is written in. -/
theorem lemma_4_1 {d : ℕ} {m : ℝ} (hm : 0 < m) (a : ℕ → ℝ)
    (x g : ℕ → EuclideanSpace ℝ (Fin d)) (k : ℕ) (hk : 1 ≤ k)
    (ha : ∀ i ∈ Finset.Icc 1 k, 0 < a i)
    (z : EuclideanSpace ℝ (Fin d)) (hz : z = -(∑ i ∈ Finset.Icc 1 k, a i • g i))
    (h : EuclideanSpace ℝ (Fin d) → ℝ)
    (hh : ∀ u, h u = ∑ i ∈ Finset.Icc 1 k, a i * inner ℝ (g i) (u - x i) + phi m a x k u) :
    (IsMinOn h Set.univ (gradient (phiStar m a x k) z) ∧
      ∀ u : EuclideanSpace ℝ (Fin d), IsMinOn h Set.univ u → u = gradient (phiStar m a x k) z) ∧
    h (gradient (phiStar m a x k) z) =
      -phiStar m a x k z - ∑ i ∈ Finset.Icc 1 k, a i * inner ℝ (g i) (x i) ∧
    (∀ (L : ℝ) (f : EuclideanSpace ℝ (Fin d) → ℝ) (xstar : EuclideanSpace ℝ (Fin d)),
      m ≤ L → ClassF m L f → IsMinOn f Set.univ xstar →
      lowerL f m a x g xstar (k + 1) ≤ f xstar) := by sorry

end AccelSGDGrowth
