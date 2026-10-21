-- Prove2me | Theorems.Thm_DerivativeChainPrivate_normalized_fifth_nonic_step
-- name    : DerivativeChainPrivate.normalized_fifth_nonic_step
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-20T22:00:18.679275+00:00
-- url     : https://prove2.me/theorems/88664894-7cbe-4896-b771-ce1462c6a36d
-- title:
--   Compatible octic-to-nonic step for a cubic fifth power
-- statement:
--   Let $q_\beta(z)=z^3-z-\beta$ with $\operatorname{Re}\beta\ge0$ and $\operatorname{Im}\beta>0$, and let $P_j$ be the monic normalization of $D^{15-j}(q_\beta^5)$. For an inverse representation $\beta/w=\alpha w^2-b+e/w$, write $A=\operatorname{Re}e/\operatorname{Re}w$, $B=\operatorname{Im}e/\operatorname{Im}w$, and $C=(3A-B)/2$.
--   Suppose $w$ is a root of $P_8$ with positive real and imaginary parts, $(\operatorname{Re}w)^2\ge7/10$, and the selected eighth-row inverse formula. There exist an actual root $z$ of $P_9$ and real $\alpha,b$ and complex $e$ such that both coordinates of $z$ are at least those of $w$,
--   $$\frac\beta z=\alpha z^2-b+\frac ez,\quad \frac{7343}{5000}<\alpha<\frac{14687}{10000},\quad\frac{12919}{10000}<b<\frac{323}{250}.$$
--   Moreover $(\operatorname{Re}z)^2>4/5$, $A\le1/16$, $B\le0$, $C\le1/8$, and $(\operatorname{Re}z)^2-3(\operatorname{Im}z)^2\ge4/5$, where the corrections are evaluated at $z$. These are the compatible ninth-row data used in the next step.
-- source:
--   https://gist.github.com/Amal-David/adce933460b7501cb123f483f62775eb/f5a76eda649f3e995a8ec6b98387b23b64c6debb#file-fifth-md; upper/H5_UPPER_BRIDGE.md, eighth-to-ninth-row bridge and row-9 inverse cubic.

import Definitions.Def_DerivativeChainPrivate_fifth_power_inverse_certificates
import Definitions.Def_DerivativeChainPrivate_fifth_row9_coefficient_bounds
import Definitions.Def_DerivativeChainPrivate_fifth_row9_newton_polynomials
import Mathlib
import Theorems.Thm_DerivativeChainPrivate_row9_complete_inverse_branches
open Polynomial MeasureTheory Filter Set DerivativeChainPrivate
open scoped Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem DerivativeChainPrivate.normalized_fifth_nonic_step (β w : ℂ) (hR : 0 ≤ β.re) (hI : 0 < β.im)
    (hwpos : 0 < w.re) (hwim : 0 < w.im) (hwX : 7/10 ≤ w.re^2)
    (hwroot : w^8-(4/3)*w^6-(8/13)*β*w^5+(20/39)*w^4+(160/429)*β*w^3-(8/143)*w^2+
      (8/143)*β^2*w^2-(16/429)*β*w+1/1287-(2/429)*β^2=0)
    (hwinv : β/w=(((22-3*Real.sqrt 22)/4:ℝ):ℂ)*w^2-(((92-9*Real.sqrt 22)/32:ℝ):ℂ)+fifthOcticRemainder w/w) :
    ∃ z : ℂ, ∃ α b : ℝ, ∃ e : ℂ,
      (fifthUnitP9 β).eval z=0 ∧ w.re ≤ z.re ∧ w.im ≤ z.im ∧ 4/5 < z.re^2 ∧
      7343/5000 < α ∧ α < 14687/10000 ∧ 12919/10000 < b ∧ b < 323/250 ∧
      β/z=(α:ℂ)*z^2-(b:ℂ)+e/z ∧ e.re/z.re ≤ 1/16 ∧ e.im/z.im ≤ 0 ∧
      (3*(e.re/z.re)-e.im/z.im)/2 ≤ 1/8 ∧ 4/5 ≤ z.re^2-3*z.im^2 := by sorry
