-- Prove2me | Theorems.Thm_ApproachRegret_Calibration_display12_dist_le_regret
-- name    : ApproachRegret.Calibration.display12_dist_le_regret
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T15:29:19.734233+00:00
-- url     : https://prove2.me/theorems/38219718-9fdb-4f9f-88b0-9d34041bddc2
-- title:
--   Display (12) — the ℓ₁ distance of the average payoff to $B_1(\varepsilon/2)$ is at most $\mathrm{Regret}_T/T$
-- statement:
--   Let $m\ge1$, $\varepsilon=1/m$ and $T\ge1$. Let $w_1,\dots,w_T\in\Delta_{m+1}$, outcomes $y_1,\dots,y_T\in[0,1]$ and points $\theta_1,\dots,\theta_T\in B_\infty(1)$ satisfy the oracle guarantee
--   $\langle u(w_t,y_t),\theta_t\rangle\le\varepsilon/2$ for every $t$. If the average payoff $\bar u_T=\frac1T\sum_{t=1}^Tu(w_t,y_t)$ lies outside $B_1(\varepsilon/2)$, then
--   $$\mathrm{dist}_1\bigl(\bar u_T,B_1(\varepsilon/2)\bigr)=\max\Bigl\{0,\|\bar u_T\|_1-\frac\varepsilon2\Bigr\}\le\frac1T\Bigl(\sum_{t=1}^T\langle -u(w_t,y_t),\theta_t\rangle-\min_{\theta\in B_\infty(1)}\sum_{t=1}^T\langle -u(w_t,y_t),\theta\rangle\Bigr).$$
--
--   The right-hand side is $1/T$ times the regret of the points $\theta_t$ against the linear losses $f_t=-u(w_t,y_t)$ on the cube. This is the guarantee (12) that reduces calibration to online linear optimization.
--
--   **Formalization Note** The left-hand side is written in the closed form of Claim 1 rather than as a distance. The hypothesis $\bar u_T\notin B_1(\varepsilon/2)$ is the page's (the derivation uses (13), stated for $x\notin B_1(\varepsilon/2)$); without it the regret may be negative and the inequality can fail. The minimum over the cube is `sInf` of the image of the (nonempty, compact) cube.
-- source:
--   Abernethy, Bartlett, Hazan (COLT 2011, JMLR W&CP 19), condition 3, display (12), and the derivation after (13), p. 42

import Mathlib
import Definitions.Def_ApproachRegret_Calibration_Game

namespace ApproachRegret.Calibration

/-- Display (12) for the calibration game (p. 42): if `θ₁, …, θ_T ∈ B∞(1)` and
`⟨u(w_t, y_t), θ_t⟩ ≤ ε/2` for every `t`, and the average payoff `ū = (1/T) ∑ₜ u(w_t, y_t)` lies
outside `B₁(ε/2)`, then `dist₁(ū, B₁(ε/2)) = max {0, ‖ū‖₁ − ε/2}` is at most `1/T` times the
regret of `θ₁, …, θ_T` against the losses `f_t = −u(w_t, y_t)` on `B∞(1)`. -/
theorem display12_dist_le_regret (m T : ℕ) (hm : 1 ≤ m) (hT : 1 ≤ T)
    (w : ℕ → Fin (m + 1) → ℝ) (y : ℕ → ℝ) (θ : ℕ → ApproachRegret.ToOLO.E (m + 1))
    (hw : ∀ t, 1 ≤ t → t ≤ T → w t ∈ stdSimplex ℝ (Fin (m + 1)))
    (hy : ∀ t, 1 ≤ t → t ≤ T → y t ∈ Set.Icc (0 : ℝ) 1)
    (hθ : ∀ t, 1 ≤ t → t ≤ T → θ t ∈ cube (m + 1))
    (horacle : ∀ t, 1 ≤ t → t ≤ T → inner ℝ (payoff m (w t) (y t)) (θ t) ≤ eps m / 2)
    (hout : eps m / 2 < l1norm (avgPayoff m T w y)) :
    max 0 (l1norm (avgPayoff m T w y) - eps m / 2)
      ≤ (1 / (T : ℝ)) * linRegret (cube (m + 1)) T (fun t => -payoff m (w t) (y t)) θ := by sorry

end ApproachRegret.Calibration
