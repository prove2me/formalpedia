-- Prove2me | Theorems.Thm_AdaptiveStepIPM_WideNbhd_theta2_lower_bound
-- name    : AdaptiveStepIPM.WideNbhd.theta2_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:45:09.351885+00:00
-- url     : https://prove2.me/theorems/3ae1af8e-4e30-42e8-b5d6-10e42818ac60
-- title:
--   Proof of Theorem 2 — $\|Pq\|^-_\infty\le\|Pq\|_\infty\le\|r\|^2/4\le n\mu/4$, hence $\theta_2^-\ge\theta_2\ge 4\beta\gamma/n$
-- statement:
--   Let $n\ge2$, $\beta,\gamma\in(0,1)$ with $\gamma\le2(1-\beta)$, let $(x,s)\in\mathcal N^-_\infty(\beta)$ with $\mu = x^Ts/n$, let $(d_x,d_y,d_s)$ solve (2) at $(x,s)$ with parameter $\gamma$, and let $p,q,r$ be the scaled vectors (6). Then
--   $$
--   \|Pq\|^-_\infty\le\|Pq\|_\infty\le\frac{\|r\|^2}{4}\le\frac{n\mu}{4},
--   \qquad\text{hence}\qquad
--   \theta_2^-\ \ge\ \theta_2\ \ge\ \frac{4\beta\gamma}{n},
--   $$
--   where $\theta_2 = \min\{1,\beta\gamma\mu/\|Pq\|_\infty\}$ and $\theta_2^- = \min\{1,\beta\gamma\mu/\|Pq\|^-_\infty\}$ are the step bounds of Lemma 5.
--
--   Since $\mathcal N_\infty(\beta)\subset\mathcal N^-_\infty(\beta)$, this covers every iterate of Algorithm 2 with either neighbourhood, and gives a step length of order $1/n$.
--
--   **Formalization Note** The paper writes this in the proof of Theorem 2 without a condition on $n$. The bound $\min\{1,\cdot\}\ge4\beta\gamma/n$ needs $4\beta\gamma/n\le1$, which holds for $n\ge2$ because $\beta\gamma\le2\beta(1-\beta)\le1/2$, but can fail for $n=1$ (e.g. $\beta = 1/2$, $\gamma = 0.9$). For $n=1$ Algorithm 2 makes no iteration at all (the largest step does not exist), so the hypothesis $n\ge2$ loses nothing for Theorem 2. A zero norm makes the corresponding bound $1$, as in Lemma 5.
-- source:
--   Mizuno, Todd, Ye, On adaptive-step primal-dual interior-point algorithms for linear programming, Cornell ORIE Technical Report No. 944 (1990, rev. 1991), p. 10, proof of Theorem 2

import Mathlib
import Definitions.Def_AdaptiveStepIPM_WideNbhd_Neighborhoods
import Definitions.Def_AdaptiveStepIPM_WideNbhd_Algorithm2

namespace AdaptiveStepIPM.WideNbhd

open Matrix

/-- Proof of Theorem 2 of Mizuno–Todd–Ye (p. 10): for `β, γ ∈ (0, 1)` with `γ ≤ 2(1 − β)`,
`(x, s) ∈ N_∞⁻(β)` and a solution `d` of (2) at `(x, s)` with `γ`,
`‖AdaptiveStepIPM.PredCorr.Pq‖⁻_∞ ≤ ‖AdaptiveStepIPM.PredCorr.Pq‖_∞ ≤ ‖r‖²/4 ≤ nμ/4`, hence `θ₂⁻ ≥ θ₂ ≥ 4βγ/n`. The last step needs `n ≥ 2`. -/
theorem theta2_lower_bound {n m : ℕ} (hn : 2 ≤ n) (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (β γ : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ)
    (hγ1 : γ < 1) (hγβ : γ ≤ 2 * (1 - β)) (x s : Fin n → ℝ) (hN : (x, s) ∈ NinfMinus A b c β)
    (dx : Fin n → ℝ) (dy : Fin m → ℝ) (ds : Fin n → ℝ) (hd : IsDirection A x s γ dx dy ds) :
    normInfNeg (AdaptiveStepIPM.PredCorr.Pq x s dx ds) ≤ normInf (AdaptiveStepIPM.PredCorr.Pq x s dx ds) ∧
      normInf (AdaptiveStepIPM.PredCorr.Pq x s dx ds) ≤ norm2 (rvec γ x s) ^ 2 / 4 ∧
      norm2 (rvec γ x s) ^ 2 / 4 ≤ (n : ℝ) * AdaptiveStepIPM.PredCorr.mu x s / 4 ∧
      stepBound β γ (AdaptiveStepIPM.PredCorr.mu x s) (normInf (AdaptiveStepIPM.PredCorr.Pq x s dx ds)) ≤
        stepBound β γ (AdaptiveStepIPM.PredCorr.mu x s) (normInfNeg (AdaptiveStepIPM.PredCorr.Pq x s dx ds)) ∧
      4 * β * γ / n ≤ stepBound β γ (AdaptiveStepIPM.PredCorr.mu x s) (normInf (AdaptiveStepIPM.PredCorr.Pq x s dx ds)) := by sorry

end AdaptiveStepIPM.WideNbhd
