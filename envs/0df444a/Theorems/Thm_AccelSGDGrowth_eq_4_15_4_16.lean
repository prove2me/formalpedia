-- Prove2me | Theorems.Thm_AccelSGDGrowth_eq_4_15_4_16
-- name    : AccelSGDGrowth.eq_4_15_4_16
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:33:56.421178+00:00
-- url     : https://prove2.me/theorems/cbe5c33c-f0c6-48f4-ab71-88277c0d4c19
-- title:
--   (4.15)–(4.16) — the pointwise one-step inequality for $A_kV_{k+1}-A_{k-1}V_k$
-- statement:
--   Let $0<m\le\mathcal L$, $f\in\mathcal F(m,\mathcal L)$ with minimizer $x_\star$, positive weights $(a_k)$, real step sizes $(\eta_k)$, and a run $x,y,z,g$ of DAM+ (4.6). Write $\varepsilon_k=g_k-\nabla f(x_k)$, $m_k=A_km$ and $V_k=f(y_k)-L_k$. For every $k\ge1$:
--
--   1. (4.15) $f(y_{k+1})-f(x_k)\le\Big(\dfrac{\mathcal L\eta_k^2}{2}-\eta_k\Big)\|g_k\|^2+\eta_k\varepsilon_k^\top g_k$;
--   2. (4.16)
--   $$
--   A_kV_{k+1}-A_{k-1}V_k\le-A_k\eta_k\Big(1-\frac{\mathcal L\eta_k}2\Big)\|g_k\|^2+A_k\eta_k\varepsilon_k^\top g_k+a_k\varepsilon_k^\top\big(x_\star-\nabla\phi_k^\star(z_k)\big)+\frac{a_k^2}{2m_k}\|g_k\|^2 .
--   $$
--
--   Taking expectations in (4.16) gives Theorem 4.1.
--
--   Differences from the source:
--   - encoding: f ∈ F(m, L), m-strongly convex with condition number κ = L/m → 0 < m and m ≤ L as hypotheses; reason: strong convexity and κ = L/m need m > 0; (1.2) forces m ≤ L whenever d ≥ 1, so only the trivial case d = 0 is affected
--   - reading: the chains (4.15) and (4.16) → first expression ≤ last expression of each chain; reason: the endpoints are the inequalities used afterwards; the intermediate expressions are steps of the proof
-- source:
--   Chen, Na, Kolar, Convergence Analysis of Accelerated Stochastic Gradient Descent under the Growth Condition, arXiv:2006.06782v4 (preprint basis), https://arxiv.org/abs/2006.06782v4, (4.15) and (4.16), p.18

import Definitions.Def_AccelSGDGrowth_ClassF
import Definitions.Def_AccelSGDGrowth_IsDAMPlusRun
import Definitions.Def_AccelSGDGrowth_gapV

namespace AccelSGDGrowth

/-- Chen, Na, Kolar, arXiv:2006.06782v4, (4.15) and (4.16), p.18. Along a DAM+ run (4.6) with
positive weights, for `f ∈ F(m, L)` with minimizer `x⋆`, `ε_k = g_k − ∇f(x_k)`, `m_k = A_k m`,
`V_k = f(y_k) − L_k`, and every `k ≥ 1`:
* (4.15) `f(y_{k+1}) − f(x_k) ≤ (Lη_k²/2 − η_k)‖g_k‖² + η_k ε_kᵀ g_k`;
* (4.16) `A_k V_{k+1} − A_{k−1} V_k ≤ −A_k η_k (1 − Lη_k/2)‖g_k‖² + A_k η_k ε_kᵀ g_k
   + a_k ε_kᵀ(x⋆ − ∇φ⋆_k(z_k)) + (a_k²/(2m_k))‖g_k‖²`.

**Formalization Note.** Deterministic (pointwise), for arbitrary real step sizes `η_k`. At `k = 1`,
`A_0 V_1 = 0`. -/
theorem eq_4_15_4_16 {d : ℕ} {m L : ℝ} (hm : 0 < m) (hmL : m ≤ L)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : ClassF m L f)
    {xstar : EuclideanSpace ℝ (Fin d)} (hxstar : IsMinOn f Set.univ xstar)
    (a η : ℕ → ℝ) (ha : ∀ k : ℕ, 1 ≤ k → 0 < a k)
    (x y z g : ℕ → EuclideanSpace ℝ (Fin d)) (hrun : IsDAMPlusRun m a η x y z g)
    (k : ℕ) (hk : 1 ≤ k) :
    f (y (k + 1)) - f (x k) ≤
      (L * η k ^ 2 / 2 - η k) * ‖g k‖ ^ 2 + η k * inner ℝ (g k - gradient f (x k)) (g k) ∧
    cumWeight a k * gapV f m a x y g xstar (k + 1) -
        cumWeight a (k - 1) * gapV f m a x y g xstar k ≤
      -(cumWeight a k * η k * (1 - L * η k / 2)) * ‖g k‖ ^ 2 +
        cumWeight a k * η k * inner ℝ (g k - gradient f (x k)) (g k) +
        a k * inner ℝ (g k - gradient f (x k)) (xstar - gradient (phiStar m a x k) (z k)) +
        a k ^ 2 / (2 * (cumWeight a k * m)) * ‖g k‖ ^ 2 := by sorry

end AccelSGDGrowth
