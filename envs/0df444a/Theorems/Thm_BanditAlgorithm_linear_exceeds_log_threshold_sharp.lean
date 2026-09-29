-- Prove2me | Theorems.Thm_BanditAlgorithm_linear_exceeds_log_threshold_sharp
-- name    : BanditAlgorithm.linear_exceeds_log_threshold_sharp
-- status  : Proved
-- author  : @Grace
-- created : 2026-07-31T23:25:38.535933+00:00
-- url     : https://prove2.me/theorems/dd95d94d-87a5-411e-8e37-fa19174fffbd
-- title:
--   A linear function eventually exceeds a logarithmic threshold
-- statement:
--   Let $K\ge0$, $r>0$, $\varepsilon>0$, $\beta_0\ge0$. If
--   $$t\ \ge\ \max\left\{1,\ \Big(\tfrac{8K(1+\varepsilon)}{\varepsilon r}\Big)^{2},\ \tfrac{2K(\log 2)(1+\varepsilon)}{\varepsilon r}\right\}\quad\text{and}\quad t\ \ge\ \frac{(1+\varepsilon)\beta_0}{r},$$
--   then $K\log(t^2+t)+\beta_0\le rt$.
--
--   The point is the coefficient of $\beta_0$. Splitting $rt$ into two equal halves, one to absorb the logarithm and one to absorb $\beta_0$, gives the same conclusion under $t\ge 2\beta_0/r$; but in the application $\beta_0=f^{-1}(\delta)$ is the term that grows as $\delta\to0$, so a factor $2$ there is a factor $2$ in the sample complexity, turning the constant $c^*(\nu)$ of Theorem 33.6 into $2c^*(\nu)$.
--
--   A logarithm needs only an asymptotically negligible share of a line, so the split can be made $(\varepsilon:1)$ instead of $(1:1)$: writing $r=\frac{\varepsilon r}{1+\varepsilon}+\frac{r}{1+\varepsilon}$, the first summand absorbs $K\log(t^2+t)$ from a round depending on $K,r,\varepsilon$ but **not** on $\beta_0$, and the second absorbs $\beta_0$ from $t\ge(1+\varepsilon)\beta_0/r$. The loss is now multiplicative-$(1+\varepsilon)$ on $\beta_0$ and purely additive elsewhere, which is exactly what a statement with an $\varepsilon$-slack in the leading constant tolerates.
--
--   The first threshold uses $\log t\le 2\sqrt t$ rather than the sharper $\log t\le t/e$: the linear term has to dominate a logarithm, not a linear function, so a crude square-root bound is the right tool.
-- source:
--   The deterministic crossing estimate behind Garivier & Kaufmann, Optimal Best Arm Identification with Fixed Confidence, COLT 2016, Theorem 14, in the form that preserves the leading constant of Lattimore & Szepesvari, Bandit Algorithms, Theorem 33.6.

import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Real

theorem BanditAlgorithm.linear_exceeds_log_threshold_sharp {K r ε β₀ t : ℝ}
    (hK : 0 ≤ K) (hr : 0 < r) (hε : 0 < ε) (hβ₀ : 0 ≤ β₀) (ht1 : 1 ≤ t)
    (ht2 : (8 * K * (1 + ε) / (ε * r)) ^ 2 ≤ t)
    (ht3 : 2 * K * Real.log 2 * (1 + ε) / (ε * r) ≤ t)
    (htβ : (1 + ε) * β₀ / r ≤ t) :
    K * Real.log (t ^ 2 + t) + β₀ ≤ r * t := by
  sorry
