-- Prove2me | Theorems.Thm_ApproachRegret_Calibration_ogd_regret_bound
-- name    : ApproachRegret.Calibration.ogd_regret_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T15:44:53.924985+00:00
-- url     : https://prove2.me/theorems/f6dbf82e-e35e-4598-b49e-3b64ec722c50
-- title:
--   Online gradient descent has regret at most $DG\sqrt T$ for linear losses
-- statement:
--   Let $\mathcal K\subseteq\mathbb R^n$ be nonempty, closed and convex, let $T\ge1$, and let $D,G>0$. Let $\theta_1\in\mathcal K$ with $\|\theta-\theta_1\|_2\le D$ for every $\theta\in\mathcal K$, and let $g_1,\dots,g_T$ be loss vectors with $\|g_t\|_2\le G$. If $\theta_2,\dots,\theta_{T+1}$ are produced by online gradient descent with step size $\eta=D/(G\sqrt T)$,
--   $\theta_{t+1}=\Pi_{\mathcal K}(\theta_t-\eta g_t)$, then
--   $$\sum_{t=1}^T\langle g_t,\theta_t\rangle-\min_{\theta\in\mathcal K}\sum_{t=1}^T\langle g_t,\theta\rangle\ \le\ D\,G\,\sqrt T .$$
--
--   This is Zinkevich's regret bound for online gradient descent, which the proof of Theorem 22 invokes for the cube $B_\infty(1)$ and the losses $-u(w_t,y_t)$.
--
--   **Formalization Note** The page states the bound with $D$ "the ℓ₂ diameter of the set". The statement assumes only $\|\theta-\theta_1\|_2\le D$ on $\mathcal K$, which the diameter implies because $\theta_1\in\mathcal K$; this is the form Theorem 22 needs, with $D=\sqrt{m+1}$ about $\theta_1=0$. The step size is pinned to $\eta=D/(G\sqrt T)$, the tuning under which the bound holds; the page's Algorithm 4 says only $\eta=O(T^{-1/2})$. The minimum is `sInf` of the image of $\mathcal K$, which is bounded.
-- source:
--   Abernethy, Bartlett, Hazan (COLT 2011, JMLR W&CP 19), Algorithm 4 and proof of Theorem 22, p. 44

import Mathlib
import Definitions.Def_ApproachRegret_Calibration_Game
import Definitions.Def_ApproachRegret_Calibration_Algorithms

namespace ApproachRegret.Calibration

/-- Proof of Theorem 22 (p. 44): Online Gradient Descent guarantees regret at most `D G √T`.
For a nonempty closed convex `K ⊆ ℝⁿ`, a start `θ₁ ∈ K` with `‖θ − θ₁‖ ≤ D` on `K`, linear
losses with `‖g_t‖ ≤ G`, and step size `η = D / (G √T)`, the OGD iterates satisfy
`∑_{t=1}^T ⟨g_t, θ_t⟩ − min_{θ ∈ K} ∑_{t=1}^T ⟨g_t, θ⟩ ≤ D G √T`. -/
theorem ogd_regret_bound {n : ℕ} (K : Set (ApproachRegret.ToOLO.E n)) (hKne : K.Nonempty) (hKc : IsClosed K)
    (hKcvx : Convex ℝ K) (T : ℕ) (hT : 1 ≤ T) (D G : ℝ) (hD : 0 < D) (hG : 0 < G)
    (g θ : ℕ → ApproachRegret.ToOLO.E n) (hθ1 : θ 1 ∈ K) (hdiam : ∀ x ∈ K, ‖x - θ 1‖ ≤ D)
    (hg : ∀ t, 1 ≤ t → t ≤ T → ‖g t‖ ≤ G)
    (hrun : IsOGDRun K (D / (G * Real.sqrt T)) T g θ) :
    linRegret K T g θ ≤ D * G * Real.sqrt T := by sorry

end ApproachRegret.Calibration
