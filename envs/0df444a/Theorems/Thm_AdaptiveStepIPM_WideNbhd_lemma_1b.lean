-- Prove2me | Theorems.Thm_AdaptiveStepIPM_WideNbhd_lemma_1b
-- name    : AdaptiveStepIPM.WideNbhd.lemma_1b
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:45:24.298126+00:00
-- url     : https://prove2.me/theorems/d04b56c4-6da7-46f5-886b-0358f252329a
-- title:
--   Lemma 1(b) — $-\|r\|^2/4 \le p_jq_j \le r_j^2/4$ for each $j$
-- statement:
--   Let $x,s\in\mathbb R^n$ be positive, $\gamma\in[0,1]$, $\mu = x^Ts/n$, and let $(d_x,d_y,d_s)$ solve the Newton system (2)
--   $$
--   Sd_x + Xd_s = \gamma\mu e - Xs,\qquad Ad_x = 0,\qquad A^Td_y + d_s = 0 .
--   $$
--   With the scaled vectors (6), $p_j = \sqrt{s_j/x_j}\,(d_x)_j$, $q_j=\sqrt{x_j/s_j}\,(d_s)_j$, $r_j = (\gamma\mu - x_js_j)/\sqrt{x_js_j}$, and $\|\cdot\|$ the Euclidean norm, for each $j$
--   $$
--   -\frac{\|r\|^2}{4} \;\le\; p_jq_j \;\le\; \frac{r_j^2}{4}.
--   $$
--
--   The product $p_jq_j$ is the $j$-th component of the second-order term $D_xd_s$ of Newton's method; this componentwise bound is the source of every step-length estimate in the paper.
--
--   **Formalization Note** The paper states the lemma for $(x,s)$ in a neighbourhood $\mathcal N\subset\mathcal F^0$; only $x,s>0$ is assumed here. $\|r\|^2$ is the square of the explicitly defined $\ell_2$ norm.
-- source:
--   Mizuno, Todd, Ye, On adaptive-step primal-dual interior-point algorithms for linear programming, Cornell ORIE Technical Report No. 944 (1990, rev. 1991), p. 5, Lemma 1(b)

import Mathlib
import Definitions.Def_AdaptiveStepIPM_WideNbhd_Neighborhoods
import Definitions.Def_AdaptiveStepIPM_WideNbhd_Algorithm2

namespace AdaptiveStepIPM.WideNbhd

open Matrix

/-- Lemma 1(b) of Mizuno–Todd–Ye (p. 5): for a solution `d` of (2) at `x, s > 0` with
`γ ∈ [0, 1]`, and `p, q, r` as in (6), `−‖r‖²/4 ≤ p_j q_j ≤ r_j²/4` for each `j`
(`‖·‖` the `ℓ₂` norm). -/
theorem lemma_1b {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (x s : Fin n → ℝ)
    (hx : ∀ j, 0 < x j) (hs : ∀ j, 0 < s j) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (dx : Fin n → ℝ) (dy : Fin m → ℝ) (ds : Fin n → ℝ) (hd : IsDirection A x s γ dx dy ds)
    (j : Fin n) :
    -(norm2 (rvec γ x s) ^ 2 / 4) ≤ pvec x s dx j * qvec x s ds j ∧
      pvec x s dx j * qvec x s ds j ≤ rvec γ x s j ^ 2 / 4 := by sorry

end AdaptiveStepIPM.WideNbhd
