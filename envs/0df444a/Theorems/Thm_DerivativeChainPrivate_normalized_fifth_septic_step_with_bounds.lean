-- Prove2me | Theorems.Thm_DerivativeChainPrivate_normalized_fifth_septic_step_with_bounds
-- name    : DerivativeChainPrivate.normalized_fifth_septic_step_with_bounds
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-20T23:07:02.000661+00:00
-- url     : https://prove2.me/theorems/2dd97b68-0309-45f6-a36a-6d1ea109b1c8
-- title:
--   Compatible seventh-row root with the bounds needed for continuation
-- statement:
--   Let $q_\beta(z)=z^3-z-\beta$ with $\operatorname{Re}\beta\ge0$ and $\operatorname{Im}\beta>0$, and let $P_j$ be the monic normalization of $D^{15-j}(q_\beta^5)$. For an inverse representation $\beta/w=\alpha w^2-b+e/w$, write $A=\operatorname{Re}e/\operatorname{Re}w$, $B=\operatorname{Im}e/\operatorname{Im}w$, and $C=(3A-B)/2$.
--   Suppose $w$ is a root of $P_6$ with positive real and imaginary parts, $(\operatorname{Re}w)^2\ge1/2$, and its inverse representation has $\alpha=55-3\sqrt{1122}/2$, $b=10-15\sqrt{1122}/68$ and a supplied error $E_0$. Assume $A\le2821/12500$, $B\le0$, $C\le5/8$, and $(\operatorname{Re}w)^2-3(\operatorname{Im}w)^2\ge1/2$.
--   There is an actual root $z$ of $P_7$ with both coordinates no smaller than those of $w$ and
--   $$\frac\beta z=\frac{55-3\sqrt{209}}4z^2-\left(5-\frac{4\sqrt{209}}{19}\right)+\frac{R_7(z)}z,$$
--   where $R_7$ is the explicit finite radical remainder in the definition bundle. The displayed hypotheses are supplied by the preceding sixth-row construction after a positive real rescaling.
--
--   The selected output also satisfies $(\operatorname{Re}z)^2>3/5$. Evaluating $A=\operatorname{Re}R_7(z)/\operatorname{Re}z$, $B=\operatorname{Im}R_7(z)/\operatorname{Im}z$ and $C=(3A-B)/2$ at that same output gives
--   $$A\le39/200,\quad B\le0,\quad C\le39/100,\quad(\operatorname{Re}z)^2-3(\operatorname{Im}z)^2\ge3/5.$$
--   This interface retains the incoming root while supplying the hypotheses for the eighth-row step.
-- source:
--   https://gist.github.com/Amal-David/adce933460b7501cb123f483f62775eb/f5a76eda649f3e995a8ec6b98387b23b64c6debb#file-fifth-md; lower/H5_LOWER_MIDDLE_COMPLETION.md, selected seventh-row localization and continuation estimates.

import Definitions.Def_DerivativeChainPrivate_fifth_power_inverse_certificates
import Mathlib
import Theorems.Thm_DerivativeChainPrivate_normalized_fifth_septic_step
open Polynomial MeasureTheory Filter Set DerivativeChainPrivate
open scoped Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem DerivativeChainPrivate.normalized_fifth_septic_step_with_bounds (β w E₀ : ℂ) (hR : 0 ≤ β.re) (hI : 0 < β.im)
    (hwpos : 0 < w.re) (hwim : 0 < w.im) (hwX : 1/2 ≤ w.re^2)
    (hwroot : (2/1001)*β^2-(20/91)*β*w^3+(40/1001)*β*w+w^6-(5/7)*w^4+(10/91)*w^2-2/1001=0)
    (hwinv : β/w = ((55-3*Real.sqrt 1122/2:ℝ):ℂ)*w^2-((10-15*Real.sqrt 1122/68:ℝ):ℂ)+E₀/w)
    (hA₀hi : E₀.re/w.re ≤ 2821/12500) (hB₀hi : E₀.im/w.im ≤ 0)
    (hC₀hi : (3*(E₀.re/w.re)-E₀.im/w.im)/2 ≤ 5/8)
    (hWedge : 1/2 ≤ w.re^2-3*w.im^2) :
    ∃ z : ℂ,
      (2/143)*β^2*z-(5/13)*β*z^4+(20/143)*β*z^2-(2/429)*β+
        z^7-z^5+(10/39)*z^3-(2/143)*z=0 ∧
      w.re ≤ z.re ∧ w.im ≤ z.im ∧ 3/5 < z.re^2 ∧
      β/z = (((55-3*Real.sqrt 209)/4:ℝ):ℂ)*z^2-((5-4*Real.sqrt 209/19:ℝ):ℂ)+fifthSepticRemainder z/z ∧
      (fifthSepticRemainder z).re/z.re ≤ 39/200 ∧ (fifthSepticRemainder z).im/z.im ≤ 0 ∧
      (3*((fifthSepticRemainder z).re/z.re)-(fifthSepticRemainder z).im/z.im)/2 ≤ 39/100 ∧
      3/5 ≤ z.re^2-3*z.im^2 := by sorry
