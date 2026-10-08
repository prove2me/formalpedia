-- Prove2me | Theorems.Thm_AdaptiveStepIPM_WideNbhd_lemma_1c
-- name    : AdaptiveStepIPM.WideNbhd.lemma_1c
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:45:04.924284+00:00
-- url     : https://prove2.me/theorems/9652fd24-ec2e-4cee-b189-75d855de64d2
-- title:
--   Lemma 1(c) — $\|Pq\|^-_\infty,\ \|Pq\|_\infty \le \|r\|^2/4 \le n\|r\|_\infty^2/4$ and $\|Pq\|^+_\infty \le \|r\|_\infty^2/4$
-- statement:
--   Let $x,s\in\mathbb R^n$ be positive, $\gamma\in[0,1]$, $(d_x,d_y,d_s)$ a solution of (2) at $(x,s)$ with parameter $\gamma$, and $p,q,r$ the scaled vectors (6), $Pq = (p_jq_j)_j$. Write $\|\cdot\|$ for the Euclidean norm, $\|\cdot\|_\infty$ for the maximum norm, and $\|z\|^\mp_\infty$ for the maximum norm of the negative (positive) part of $z$. Then
--   $$
--   \|Pq\|^-_\infty \le \frac{\|r\|^2}{4} \le \frac{n\|r\|_\infty^2}{4},\qquad
--   \|Pq\|^+_\infty \le \frac{\|r\|^2_\infty}{4},\qquad
--   \|Pq\|_\infty \le \frac{\|r\|^2}{4} \le \frac{n\|r\|_\infty^2}{4}.
--   $$
--
--   These bounds on the second-order term turn the neighbourhood conditions into lower bounds on the step length (Lemma 5 and the proof of Theorem 2).
--
--   **Formalization Note** The inequality $\|r\|^2/4 \le n\|r\|^2_\infty/4$ appears twice in the paper's display and once in the Lean conjunction. Only $x,s>0$ is assumed of the pair.
-- source:
--   Mizuno, Todd, Ye, On adaptive-step primal-dual interior-point algorithms for linear programming, Cornell ORIE Technical Report No. 944 (1990, rev. 1991), p. 5, Lemma 1(c)

import Mathlib
import Definitions.Def_AdaptiveStepIPM_WideNbhd_Neighborhoods
import Definitions.Def_AdaptiveStepIPM_WideNbhd_Algorithm2

namespace AdaptiveStepIPM.WideNbhd

open Matrix

/-- Lemma 1(c) of Mizuno–Todd–Ye (p. 5): for a solution `d` of (2) at `x, s > 0` with
`γ ∈ [0, 1]`, and `p, q, r` as in (6),
`‖AdaptiveStepIPM.PredCorr.Pq‖⁻_∞ ≤ ‖r‖²/4 ≤ n‖r‖²_∞/4`, `‖AdaptiveStepIPM.PredCorr.Pq‖⁺_∞ ≤ ‖r‖²_∞/4` and `‖AdaptiveStepIPM.PredCorr.Pq‖_∞ ≤ ‖r‖²/4 ≤ n‖r‖²_∞/4`
(`‖r‖` the `ℓ₂` norm, `‖r‖_∞` the `ℓ_∞` norm). -/
theorem lemma_1c {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (x s : Fin n → ℝ)
    (hx : ∀ j, 0 < x j) (hs : ∀ j, 0 < s j) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (dx : Fin n → ℝ) (dy : Fin m → ℝ) (ds : Fin n → ℝ) (hd : IsDirection A x s γ dx dy ds) :
    normInfNeg (AdaptiveStepIPM.PredCorr.Pq x s dx ds) ≤ norm2 (rvec γ x s) ^ 2 / 4 ∧
      norm2 (rvec γ x s) ^ 2 / 4 ≤ (n : ℝ) * normInf (rvec γ x s) ^ 2 / 4 ∧
      normInfPos (AdaptiveStepIPM.PredCorr.Pq x s dx ds) ≤ normInf (rvec γ x s) ^ 2 / 4 ∧
      normInf (AdaptiveStepIPM.PredCorr.Pq x s dx ds) ≤ norm2 (rvec γ x s) ^ 2 / 4 := by sorry

end AdaptiveStepIPM.WideNbhd
