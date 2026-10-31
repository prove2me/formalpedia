-- Prove2me | Theorems.Thm_AccelSGDGrowth_lemma_4_2
-- name    : AccelSGDGrowth.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:32:41.976927+00:00
-- url     : https://prove2.me/theorems/70ca513d-f17f-4049-9999-7ae43a6a3ff1
-- title:
--   Lemma 4.2 — one-step bounds on $A_kU_{k+1}-A_{k-1}U_k$ and $A_kL_{k+1}-A_{k-1}L_k$
-- statement:
--   Let $0<m\le\mathcal L$, $f\in\mathcal F(m,\mathcal L)$ with minimizer $x_\star$, positive weights $(a_k)$, real step sizes $(\eta_k)$, and let $x,y,z,g$ be a run of DAM+ (4.6). Write $U_k=f(y_k)$, $L_k$ for (4.3), $\nabla f_k=\nabla f(x_k)$ and $\varepsilon_k=g_k-\nabla f_k$. For every $k\ge1$:
--
--   1. $A_kU_{k+1}-A_{k-1}U_k\le a_kf(x_k)+A_k\big(f(y_{k+1})-f(x_k)\big)+a_k\nabla f_k^\top\big(\nabla\phi_k^\star(z_k)-x_k\big)$;
--   2. $A_kL_{k+1}-A_{k-1}L_k=a_kf(x_k)-a_k\varepsilon_k^\top x_\star-a_k\nabla f_k^\top x_k-\phi_k^\star(z_{k+1})+\phi_{k-1}^\star(z_k)$.
--
--   The statement is deterministic (pointwise in the randomness).
--
--   Differences from the source:
--   - encoding: f ∈ F(m, L), m-strongly convex with condition number κ = L/m → 0 < m and m ≤ L as hypotheses; reason: strong convexity and κ = L/m need m > 0; (1.2) forces m ≤ L whenever d ≥ 1, so only the trivial case d = 0 is affected
--   - encoding: k = 1 with A_0 L_1 and φ⋆_0(z_1) → A_0 L_1 = 0 · (junk) and φ⋆_0(z_1) = φ⋆_0(0) = 0; reason: the paper's L_1 only appears multiplied by A_0 = 0, and z_1 = 0 is forced by (4.6a)
-- source:
--   Chen, Na, Kolar, Convergence Analysis of Accelerated Stochastic Gradient Descent under the Growth Condition, arXiv:2006.06782v4 (preprint basis), https://arxiv.org/abs/2006.06782v4, Lemma 4.2, p.17

import Definitions.Def_AccelSGDGrowth_ClassF
import Definitions.Def_AccelSGDGrowth_IsDAMPlusRun
import Definitions.Def_AccelSGDGrowth_lowerL

namespace AccelSGDGrowth

/-- Chen, Na, Kolar, arXiv:2006.06782v4, Lemma 4.2, p.17. Along a DAM+ run (4.6) with positive
weights, for `f ∈ F(m, L)` with minimizer `x⋆`, `U_k = f(y_k)`, `L_k` of (4.3), `∇f_k = ∇f(x_k)`,
`ε_k = g_k − ∇f_k`, and every `k ≥ 1`:
(a) `A_k U_{k+1} − A_{k−1} U_k ≤ a_k f(x_k) + A_k (f(y_{k+1}) − f(x_k)) + a_k ∇f_kᵀ(∇φ⋆_k(z_k) − x_k)`;
(b) `A_k L_{k+1} − A_{k−1} L_k = a_k f(x_k) − a_k ε_kᵀ x⋆ − a_k ∇f_kᵀ x_k − φ⋆_k(z_{k+1}) + φ⋆_{k−1}(z_k)`.

**Formalization Note.** Deterministic (pointwise). At `k = 1`, `A_0 L_1 = 0` (the junk `L_1` is
multiplied by `A_0 = 0`) and `φ⋆_0(z_1) = φ⋆_0(0) = 0`, since (4.6a) forces `z_1 = 0`. -/
theorem lemma_4_2 {d : ℕ} {m L : ℝ} (hm : 0 < m) (hmL : m ≤ L)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : ClassF m L f)
    {xstar : EuclideanSpace ℝ (Fin d)} (hxstar : IsMinOn f Set.univ xstar)
    (a η : ℕ → ℝ) (ha : ∀ k : ℕ, 1 ≤ k → 0 < a k)
    (x y z g : ℕ → EuclideanSpace ℝ (Fin d)) (hrun : IsDAMPlusRun m a η x y z g)
    (k : ℕ) (hk : 1 ≤ k) :
    cumWeight a k * f (y (k + 1)) - cumWeight a (k - 1) * f (y k) ≤
      a k * f (x k) + cumWeight a k * (f (y (k + 1)) - f (x k)) +
        a k * inner ℝ (gradient f (x k)) (gradient (phiStar m a x k) (z k) - x k) ∧
    cumWeight a k * lowerL f m a x g xstar (k + 1) -
        cumWeight a (k - 1) * lowerL f m a x g xstar k =
      a k * f (x k) - a k * inner ℝ (g k - gradient f (x k)) xstar -
        a k * inner ℝ (gradient f (x k)) (x k) - phiStar m a x k (z (k + 1)) +
        phiStar m a x (k - 1) (z k) := by sorry

end AccelSGDGrowth
