-- Prove2me | Theorems.Thm_AbernethyBartlettHazan2011_thm22_sampled_forecaster_faithful
-- name    : AbernethyBartlettHazan2011.thm22_sampled_forecaster_faithful
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-23T01:32:34.459957+00:00
-- url     : https://prove2.me/theorems/dd082c2b-e289-45d6-8c71-7e88dd140084
-- title:
--   Theorem 22 for the sampled forecaster: expected $(\ell_1,\varepsilon)$-calibration rate at most $2\sqrt{2/(\varepsilon T)}$
-- statement:
--   Let $m \ge 1$, $\varepsilon = 1/m$, $T \ge 1$, and let $y_1,\dots,y_T \in \{0,1\}$ be any fixed outcomes. Run Algorithm 5 of Abernethy, Bartlett and Hazan: $\theta_1 = 0$, $w_1 \in \Delta_{m+1}$ arbitrary, $\theta_{t+1} = \Pi_{B_\infty(1)}(\theta_t + \eta\, u(w_t,y_t))$ with $\eta = \sqrt{(m+1)/T}$ and $u$ the payoff of game (11), and $w_{t+1}$ an output of the oracle Algorithm 3 on $\theta_{t+1}$. The forecaster draws $i_1,\dots,i_T$ independently with $\Pr(i_t = i) = w_t(i)$ and predicts $p_t = i_t/m$. Its realized $(\ell_1,\varepsilon)$-calibration rate is
--   $$C_T^\varepsilon = \max\Big\{0,\ \sum_{i=0}^m \Big|\frac1T\sum_{t=1}^T \mathbb 1[i_t = i]\Big(\frac im - y_t\Big)\Big| - \frac\varepsilon2\Big\}.$$
--   Then
--   $$\mathbb E\big[C_T^\varepsilon\big] \le 2\sqrt{\frac{2}{\varepsilon T}}.$$
--
--   This is Theorem 22 (p. 42) of the paper for the forecaster's actual randomized predictions, in expectation over its draws, with an explicit constant. The existing theorem ApproachRegret.Calibration.theorem22_calibration_rate bounds the same expression with $\mathbb 1[i_t = i]$ replaced by $w_t(i)$ (the calibration vector's expectation) by $\sqrt{2/(\varepsilon T)}$; the present statement adds the sampling step that Lemma 20 (p. 41) describes.
--
--   **Formalization Note** Since $w_t$ depends only on $y_1,\dots,y_{t-1}$, for a fixed outcome sequence the draws are independent, so the expectation is the finite sum over $s \in \{0,\dots,m\}^T$ weighted by $\prod_t w_t(s_t)$. The sum runs over the $m+1$ grid points $0, 1/m, \dots, 1$ (Definition 19 prints $\lfloor 1/\varepsilon \rfloor$ terms); the extra term is nonnegative, so this bound implies the one with $m$ terms.
-- source:
--   Abernethy, Bartlett, Hazan, Blackwell Approachability and No-Regret Learning are Equivalent, COLT 2011, JMLR W&CP 19:27–46, https://proceedings.mlr.press/v19/abernethy11b.html, Theorem 22 (p. 42) with Definition 19 (p. 40), Lemma 20 (p. 41), Algorithm 5 and (14) (p. 44)

import Mathlib
import Definitions.Def_ApproachRegret_Calibration_Game
import Definitions.Def_ApproachRegret_Calibration_Algorithms

open ApproachRegret.Calibration

theorem AbernethyBartlettHazan2011.thm22_sampled_forecaster_faithful (m T : ℕ) (hm : 1 ≤ m) (hT : 1 ≤ T)
    (y : ℕ → ℝ) (hy : ∀ t, 1 ≤ t → t ≤ T → y t = 0 ∨ y t = 1)
    (w : ℕ → Fin (m + 1) → ℝ) (θ : ℕ → ApproachRegret.ToOLO.E (m + 1))
    (hrun : IsAlg5Run m (Real.sqrt (((m : ℝ) + 1) / T)) T y w θ) :
    ∑ s : Fin T → Fin (m + 1), (∏ t : Fin T, w (t.val + 1) (s t)) *
      max 0 ((∑ i : Fin (m + 1),
          |(1 / (T : ℝ)) * ∑ t : Fin T,
            (if s t = i then (1 : ℝ) else 0) * (((i : ℕ) : ℝ) / (m : ℝ) - y (t.val + 1))|)
        - eps m / 2)
      ≤ 2 * Real.sqrt (2 / (eps m * T)) := by sorry
