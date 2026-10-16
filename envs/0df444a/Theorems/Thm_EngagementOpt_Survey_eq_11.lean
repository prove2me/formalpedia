-- Prove2me | Theorems.Thm_EngagementOpt_Survey_eq_11
-- name    : EngagementOpt.Survey.eq_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T06:18:48.093031+00:00
-- url     : https://prove2.me/theorems/60cbb64d-a29b-4c44-a367-67a6ed1d9024
-- title:
--   (11): the $t$-derivative of (10) is $\bar v\,\varphi(\beta^t-1)-W$
-- statement:
--   Let $\beta>0$ with $\beta\ne1$, $\bar v\ge0$, $W>0$, and extend the closed form (10) to real $s>0$ by
--
--   $$
--   F(s)=\bar v\left(\frac{s\beta^s}{\beta^s-1}-\frac{1}{\beta-1}\right)-Ws .
--   $$
--
--   Then for every real $t>0$:
--
--   1. $F$ is differentiable at $t$ with
--   $$
--   F'(t)=\bar v\,\varphi(\beta^t-1)-W,\qquad \varphi(x)=\frac{x+1}{x}\left(1-\frac{\ln(x+1)}{x}\right);
--   $$
--   2. if $\bar v>0$, then $F'(t)>0$ if and only if
--   $$
--   \varphi(\beta^t-1)>\frac{W}{\bar v}.
--   $$
--
--   With $x=\beta^t-1$ (so that $t\ln\beta=\ln(x+1)$), this is the criterion (11) for $\mathbb E[S\mid T=t]$ to be increasing in $t$.
--
--   **Formalization Note** $\beta^s$ is the real power $\beta^s=e^{s\ln\beta}$. On natural numbers it agrees with the natural-number power used in (10). The paper derives (11) in the case $q>p$ ($\beta>1$) and reuses it for $q<p$; the identity is stated for every $\beta>0$, $\beta\ne1$.
-- source:
--   Kleinberg, Mullainathan, Raghavan, The Challenge of Understanding What Users Want, arXiv:2202.11776v3, p. 21, display chain ending in (11)

import Mathlib
import Definitions.Def_EngagementOpt_Survey_phi

namespace EngagementOpt.Survey

/-- arXiv:2202.11776v3, p. 21, the derivative computation ending in (11). Extend (10) to real
`s > 0` with `β ^ s = Real.rpow β s`. For `β > 0`, `β ≠ 1`, `v̄ ≥ 0`, `W > 0`, and real `t > 0`, the derivative of
`s ↦ v̄ (s β^s/(β^s - 1) - 1/(β - 1)) - W s` at `t` is `v̄ φ(β^t - 1) - W`, where
`φ(x) = (x + 1)/x · (1 - ln(x + 1)/x)`; and when `v̄ > 0` this derivative is positive exactly
when `φ(β^t - 1) > W/v̄`. -/
theorem eq_11 (β : ℝ) (hβ0 : 0 < β) (hβ1 : β ≠ 1) (v W t : ℝ)
    (hv : 0 ≤ v) (hW : 0 < W) (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => v * (s * β ^ s / (β ^ s - 1) - 1 / (β - 1)) - W * s)
      (v * phi (β ^ t - 1) - W) t ∧
    (0 < v → (0 < v * phi (β ^ t - 1) - W ↔ W / v < phi (β ^ t - 1))) := by sorry

end EngagementOpt.Survey
