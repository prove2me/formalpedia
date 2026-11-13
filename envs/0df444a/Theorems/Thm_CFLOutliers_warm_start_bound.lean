-- Prove2me | Theorems.Thm_CFLOutliers_warm_start_bound
-- name    : CFLOutliers.warm_start_bound
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T22:34:57.686497+00:00
-- url     : https://prove2.me/theorems/0e7e0bbc-1045-4648-a148-4c77292de5e4
-- title:
--   §2.3, (6)–(7) — the warm-start bound $\min\{b,a+\theta b+M\}\le\frac{12}{11}H+M$
-- statement:
--   Let $a,b,\theta,t,H,M$ be real numbers with $0<\theta\le 1$, $t\ge 0$, $H\ge 0$ and $M\ge 0$, satisfying the two endpoint bounds
--
--   $$a\le H-3\theta t,\qquad b\le a+t.\tag{6}$$
--
--   Then
--
--   $$\min\{b,\ a+\theta b+M\}\le\frac{12}{11}H+M.\tag{7}$$
--
--   In the paper $a=c(S^-)$, $b=c(S^+)$, $t=\lambda^+(q^+-q^-)$ and $H=5\,\mathrm{OPT}+6m\tau+3n\eta$; the bound turns the signed comparison and the warm start into the factor $\frac{12}{11}\cdot 5=\frac{60}{11}$. The constant $12/11$ is attained at $\theta=1/6$, $t=2H/11$.
--
--   Differences from the source:
--   - generalization: a = c(S⁻), b = c(S⁺), θ the merge parameter, t = λ⁺g, H = 5 OPT + 6mτ + 3nη → arbitrary reals with 0 < θ ≤ 1, t ≥ 0, H ≥ 0, M ≥ 0 satisfying (6); reason: the derivation on pp.6–7 uses only (6) and these sign conditions, all of which the paper's values satisfy
-- source:
--   R. Dabas, A Constant-Factor Approximation for Capacitated Facility Location with Outliers, arXiv:2611.04094 (preprint; held version, sha256 613f7405…9798), §2.3, pp.6–7, displays (6)–(7)

import Mathlib

namespace CFLOutliers

/-- **The warm-start bound** (Dabas, arXiv:2611.04094, §2.3, displays (6)–(7), pp.6–7).
For reals with `0 < θ ≤ 1`, `t ≥ 0`, `H ≥ 0`, `M ≥ 0`, if `a ≤ H − 3θt` and `b ≤ a + t` (6),
then `min{b, a + θ b + M} ≤ (12/11) H + M` (7).

**Formalization Note.** Stated for arbitrary reals meeting (6); in the paper `a = c(S⁻)`,
`b = c(S⁺)`, `t = λ⁺ g`, `H = 5 OPT + 6mτ + 3nη ≥ 0`. -/
theorem warm_start_bound (a b θ t H M : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (ht : 0 ≤ t)
    (hH : 0 ≤ H) (hM : 0 ≤ M) (ha : a ≤ H - 3 * θ * t) (hb : b ≤ a + t) :
    min b (a + θ * b + M) ≤ 12 / 11 * H + M := by sorry

end CFLOutliers
