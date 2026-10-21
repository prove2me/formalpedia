-- Prove2me | Theorems.Thm_DerivativeChainPrivate_normalized_fifth_octic_step_with_bounds
-- name    : DerivativeChainPrivate.normalized_fifth_octic_step_with_bounds
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-20T23:06:35.496419+00:00
-- url     : https://prove2.me/theorems/1a180ecc-b582-4bf5-86ae-757a89098516
-- title:
--   Compatible eighth-row root with the next-row location bound
-- statement:
--   Let $q_\beta(z)=z^3-z-\beta$ with $\operatorname{Re}\beta\ge0$ and $\operatorname{Im}\beta>0$, and let $P_j$ be the monic normalization of $D^{15-j}(q_\beta^5)$. For an inverse representation $\beta/w=\alpha w^2-b+e/w$, write $A=\operatorname{Re}e/\operatorname{Re}w$, $B=\operatorname{Im}e/\operatorname{Im}w$, and $C=(3A-B)/2$.
--   Suppose $w$ is a root of $P_7$, has positive real and imaginary parts and $(\operatorname{Re}w)^2\ge3/5$, and satisfies the selected seventh-row inverse formula with remainder $R_7$. Assume $A\le39/200$, $B\le0$, $C\le39/100$, and $(\operatorname{Re}w)^2-3(\operatorname{Im}w)^2\ge3/5$.
--   There is an actual root $z$ of $P_8$ with both coordinates no smaller than those of $w$ and
--   $$\frac\beta z=\frac{22-3\sqrt{22}}4z^2-\frac{92-9\sqrt{22}}{32}+\frac{R_8(z)}z.$$
--   Here $R_8$ is the explicit finite radical remainder in the definition bundle. These incoming bounds are established by the selected seventh-row estimates.
--
--   The same selected output satisfies
--   $$(\operatorname{Re}z)^2>7/10.$$
--   This strengthens the compatible eighth-row step with the location bound required to apply the ninth-row inverse-cubic cover.
-- source:
--   https://gist.github.com/Amal-David/adce933460b7501cb123f483f62775eb/f5a76eda649f3e995a8ec6b98387b23b64c6debb#file-fifth-md; lower/H5_LOWER_MIDDLE_COMPLETION.md, selected eighth-row localization.

import Definitions.Def_DerivativeChainPrivate_fifth_power_inverse_certificates
import Mathlib
import Theorems.Thm_DerivativeChainPrivate_normalized_fifth_octic_step
open Polynomial MeasureTheory Filter Set DerivativeChainPrivate
open scoped Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem DerivativeChainPrivate.normalized_fifth_octic_step_with_bounds (β w : ℂ) (hR : 0 ≤ β.re) (hI : 0 < β.im)
    (hwpos : 0 < w.re) (hwim : 0 < w.im) (hwX : 3/5 ≤ w.re^2)
    (hwroot : (2/143)*β^2*w-(5/13)*β*w^4+(20/143)*β*w^2-(2/429)*β+
      w^7-w^5+(10/39)*w^3-(2/143)*w=0)
    (hwinv : β/w = (((55-3*Real.sqrt 209)/4:ℝ):ℂ)*w^2-((5-4*Real.sqrt 209/19:ℝ):ℂ)+fifthSepticRemainder w/w)
    (hA₀hi : (fifthSepticRemainder w).re/w.re ≤ 39/200)
    (hB₀hi : (fifthSepticRemainder w).im/w.im ≤ 0)
    (hC₀ : (3*((fifthSepticRemainder w).re/w.re)-(fifthSepticRemainder w).im/w.im)/2 ≤ 39/100)
    (hWedge : 3/5 ≤ w.re^2-3*w.im^2) :
    ∃ z : ℂ,
      z^8-(4/3)*z^6-(8/13)*β*z^5+(20/39)*z^4+(160/429)*β*z^3-(8/143)*z^2+
        (8/143)*β^2*z^2-(16/429)*β*z+1/1287-(2/429)*β^2=0 ∧
      w.re ≤ z.re ∧ w.im ≤ z.im ∧ 7/10 < z.re^2 ∧
      β/z = (((22-3*Real.sqrt 22)/4:ℝ):ℂ)*z^2-(((92-9*Real.sqrt 22)/32:ℝ):ℂ)+fifthOcticRemainder z/z := by sorry
