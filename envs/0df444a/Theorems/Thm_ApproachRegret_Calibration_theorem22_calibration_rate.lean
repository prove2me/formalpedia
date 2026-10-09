-- Prove2me | Theorems.Thm_ApproachRegret_Calibration_theorem22_calibration_rate
-- name    : ApproachRegret.Calibration.theorem22_calibration_rate
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T15:45:08.152978+00:00
-- url     : https://prove2.me/theorems/5da30420-aae7-4edc-a38d-513b98622158
-- title:
--   Theorem 22 with (14) — the efficient forecaster's $(\ell_1,\varepsilon)$-calibration rate is at most $\sqrt{2/(\varepsilon T)}$
-- statement:
--   Let $m\ge1$, $\varepsilon=1/m$, $T\ge1$, and let $y_1,\dots,y_T\in\{0,1\}$ be any outcomes. Run Algorithm 5: $\theta_1=0$, $w_1\in\Delta_{m+1}$ arbitrary, and for $t=1,\dots,T$, with $u_t=u(w_t,y_t)$ the payoff of game (11), online gradient descent on the cube $B_\infty(1)$ against the losses $-u_t$ with step size $\eta=\sqrt{(m+1)/T}$,
--   $$\theta_{t+1}=\Pi_{B_\infty(1)}(\theta_t+\eta u_t),$$
--   and $w_{t+1}$ an output of the oracle Algorithm 3 on $\theta_{t+1}$. Then the $(\ell_1,\varepsilon)$-calibration rate of the forecast distributions satisfies
--   $$\bar C^\varepsilon_T=\max\Bigl\{0,\ \sum_{i=0}^m\Bigl|\frac1T\sum_{t=1}^Tw_t(i)\Bigl(\frac im-y_t\Bigr)\Bigr|-\frac\varepsilon2\Bigr\}\ \le\ \sqrt{\frac{2}{\varepsilon T}} .$$
--
--   This is the explicit form $C^\varepsilon_T\le GD/\sqrt T=O(1/\sqrt{\varepsilon T})$ of the paper's bound (14): an efficient forecaster whose calibration error vanishes at rate $T^{-1/2}$ against every outcome sequence.
--
--   **Formalization Note** (1) Algorithm 4's printed step $\theta_t-\eta u_t$ is corrected to $\theta_t+\eta u_t$: the proof runs the learner on the losses $f_t=-u_t$ (condition 2, p. 42); with the printed sign the bound fails. (2) The page sets $\eta=O(T^{-1/2})$; the statement pins $\eta=\sqrt{(m+1)/T}$, the standard tuning with radius $\sqrt{m+1}$ of the cube about $\theta_1=0$ and $\|u_t\|_2\le1$. The page's $D=\sqrt{1/\varepsilon}$ is not the diameter of the cube ($2\sqrt{m+1}$); the product $GD/\sqrt T=\sqrt{2m/T}$ with the page's $G=\sqrt2$ is the bound stated. (3) The rate is that of the distributions $w_t$, i.e. the expectation of the calibration vector over the forecaster's draws (Lemma 20), which is what (12)–(14) bound; the high-probability statement for the sampled $p_t$ is not formalized. (4) The running time $O(\log 1/\varepsilon)$ is not formalized. (5) The outcomes are any fixed sequence; since $w_t$ depends only on $y_1,\dots,y_{t-1}$, this covers every adversary that does not see the forecaster's coin flips. Added hypotheses: $m\ge1$ and $T\ge1$.
-- source:
--   Abernethy, Bartlett, Hazan (COLT 2011, JMLR W&CP 19), Theorem 22, p. 42, with (14), p. 44

import Mathlib
import Definitions.Def_ApproachRegret_Calibration_Game
import Definitions.Def_ApproachRegret_Calibration_Algorithms

namespace ApproachRegret.Calibration

/-- Theorem 22 (p. 42) in the explicit form (14) of its proof (p. 44): with `ε = 1/m`, `m ≥ 1`,
horizon `T ≥ 1`, any outcomes `y₁, …, y_T ∈ {0, 1}`, and every run of Algorithm 5 (Algorithm 3 as
oracle, OGD on `B∞(1)` with step `η = √((m+1)/T)` against the losses `−u_t`), the
`(ℓ₁, ε)`-calibration rate of the forecast distributions is at most `√(2/(εT))`. -/
theorem theorem22_calibration_rate (m T : ℕ) (hm : 1 ≤ m) (hT : 1 ≤ T) (y : ℕ → ℝ)
    (hy : ∀ t, 1 ≤ t → t ≤ T → y t = 0 ∨ y t = 1)
    (w : ℕ → Fin (m + 1) → ℝ) (θ : ℕ → ApproachRegret.ToOLO.E (m + 1))
    (hrun : IsAlg5Run m (Real.sqrt (((m : ℝ) + 1) / T)) T y w θ) :
    calibRate m T w y ≤ Real.sqrt (2 / (eps m * T)) := by sorry

end ApproachRegret.Calibration
