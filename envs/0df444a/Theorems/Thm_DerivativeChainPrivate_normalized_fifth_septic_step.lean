-- Prove2me | Theorems.Thm_DerivativeChainPrivate_normalized_fifth_septic_step
-- name    : DerivativeChainPrivate.normalized_fifth_septic_step
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-20T18:50:56.277198+00:00
-- url     : https://prove2.me/theorems/9c203615-ffa4-4542-b127-8f5a07e0a00e
-- title:
--   Compatible selected sextic-to-septic step for a cubic fifth power
-- statement:
--   Let $q_\beta(z)=z^3-z-\beta$ with $\operatorname{Re}\beta\ge0$ and $\operatorname{Im}\beta>0$, and let $P_j$ be the monic normalization of $D^{15-j}(q_\beta^5)$. For an inverse representation $\beta/w=\alpha w^2-b+e/w$, write $A=\operatorname{Re}e/\operatorname{Re}w$, $B=\operatorname{Im}e/\operatorname{Im}w$, and $C=(3A-B)/2$.
--   Suppose $w$ is a root of $P_6$ with positive real and imaginary parts, $(\operatorname{Re}w)^2\ge1/2$, and its inverse representation has $\alpha=55-3\sqrt{1122}/2$, $b=10-15\sqrt{1122}/68$ and a supplied error $E_0$. Assume $A\le2821/12500$, $B\le0$, $C\le5/8$, and $(\operatorname{Re}w)^2-3(\operatorname{Im}w)^2\ge1/2$.
--   There is an actual root $z$ of $P_7$ with both coordinates no smaller than those of $w$ and
--   $$\frac\beta z=\frac{55-3\sqrt{209}}4z^2-\left(5-\frac{4\sqrt{209}}{19}\right)+\frac{R_7(z)}z,$$
--   where $R_7$ is the explicit finite radical remainder in the definition bundle. The displayed hypotheses are supplied by the preceding sixth-row construction after a positive real rescaling.
-- source:
--   https://gist.github.com/Amal-David/adce933460b7501cb123f483f62775eb/f5a76eda649f3e995a8ec6b98387b23b64c6debb#file-fifth-md; lower/H5_LOWER_MIDDLE_COMPLETION.md, seventh-row construction.

import Definitions.Def_DerivativeChainPrivate_fifth_power_inverse_certificates
import Mathlib
open Polynomial MeasureTheory Filter Set DerivativeChainPrivate
open scoped Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem DerivativeChainPrivate.normalized_fifth_septic_step (β w E₀ : ℂ) (hR : 0 ≤ β.re) (hI : 0 < β.im)
    (hwpos : 0 < w.re) (hwim : 0 < w.im) (hwX : 1/2 ≤ w.re^2)
    (hwroot : (2/1001)*β^2-(20/91)*β*w^3+(40/1001)*β*w+w^6-(5/7)*w^4+(10/91)*w^2-2/1001=0)
    (hwinv : β/w = ((55-3*Real.sqrt 1122/2:ℝ):ℂ)*w^2-((10-15*Real.sqrt 1122/68:ℝ):ℂ)+E₀/w)
    (hA₀hi : E₀.re/w.re ≤ 2821/12500) (hB₀hi : E₀.im/w.im ≤ 0)
    (hC₀hi : (3*(E₀.re/w.re)-E₀.im/w.im)/2 ≤ 5/8)
    (hWedge : 1/2 ≤ w.re^2-3*w.im^2) :
    ∃ z : ℂ,
      (2/143)*β^2*z-(5/13)*β*z^4+(20/143)*β*z^2-(2/429)*β+
        z^7-z^5+(10/39)*z^3-(2/143)*z=0 ∧
      w.re ≤ z.re ∧ w.im ≤ z.im ∧
      β/z = (((55-3*Real.sqrt 209)/4:ℝ):ℂ)*z^2-((5-4*Real.sqrt 209/19:ℝ):ℂ)+fifthSepticRemainder z/z := by sorry
