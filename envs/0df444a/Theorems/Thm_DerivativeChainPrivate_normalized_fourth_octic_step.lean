-- Prove2me | Theorems.Thm_DerivativeChainPrivate_normalized_fourth_octic_step
-- name    : DerivativeChainPrivate.normalized_fourth_octic_step
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-20T15:48:09.779503+00:00
-- url     : https://prove2.me/theorems/76a44ec7-918f-4cd8-94ce-738d7094f465
-- title:
--   Compatible selected septic-to-octic step for a cubic fourth power
-- statement:
--   Use the common normalization $q_0(z)=z^3-\frac{11}{2}z-55\beta$, with $\operatorname{Re}\beta\ge0$ and $\operatorname{Im}\beta>0$. Suppose $w$ is an actual seventh-row root with positive real and imaginary parts, $(\operatorname{Re}w)^2\ge4$, and
--   $$\frac{\beta}{w}=\frac{7-3\sqrt3}{55}w^2-\frac{7(3-\sqrt3)}{60}+\frac{R_7(w)}{w}.$$
--   There exists an actual eighth-row root $z$ with both coordinates at least those of $w$ and with selected inverse identity
--   $$\frac{\beta}{z}=\frac{28-3\sqrt{26}}{550}z^2-\frac{1274-99\sqrt{26}}{6500}+\frac{R_8(z)}{z}.$$
--   The functions $R_7,R_8$ are the explicit radical remainders in the imported definitions. The actual octic equation is
--   $$z^8-\frac{28}{3}z^6-56\beta z^5+\frac{77}{3}z^4+\frac{770}{3}\beta z^3-\frac{121}{6}z^2+550\beta^2z^2-\frac{605}{3}\beta z+\frac{1331}{720}-\frac{1210}{3}\beta^2=0.$$
--   The conclusion uses the same incoming point and parameter and supplies the branch needed for the source-root step.
-- source:
--   https://gist.github.com/Amal-David/adce933460b7501cb123f483f62775eb (revision f5a76eda649f3e995a8ec6b98387b23b64c6debb); complex/H4_COMPLETE_CHAIN.md, seventh-to-eighth row link; cone/OCTIC_H4_INVERSE_MEASURE.md, §§1–2, for the actual inverse equation.

import Definitions.Def_DerivativeChainPrivate_higher_power_radicals
import Mathlib
open Polynomial MeasureTheory Filter Set DerivativeChainPrivate
open scoped Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

theorem DerivativeChainPrivate.normalized_fourth_octic_step (β w : ℂ) (hR : 0 ≤ β.re) (hI : 0 < β.im)
    (hwpos : 0 < w.re) (hwim : 0 < w.im) (hwX : 4 ≤ w.re^2)
    (hwroot : (275/2)*β^2*w-35*β*w^4+(385/4)*β*w^2-(605/24)*β+
      w^7-7*w^5+(77/6)*w^3-(121/24)*w=0)
    (hwinv : β/w = (((7-3*Real.sqrt 3)/55:ℝ):ℂ)*w^2-((7*(3-Real.sqrt 3)/60:ℝ):ℂ)+septicRemainder w/w) :
    ∃ z : ℂ,
      z^8-(28/3)*z^6-56*β*z^5+(77/3)*z^4+(770/3)*β*z^3-(121/6)*z^2+
        550*β^2*z^2-(605/3)*β*z+1331/720-(1210/3)*β^2=0 ∧
      w.re ≤ z.re ∧ w.im ≤ z.im ∧
      β/z = (((28-3*Real.sqrt 26)/550:ℝ):ℂ)*z^2-(((1274-99*Real.sqrt 26)/6500:ℝ):ℂ)+octicRemainder z/z := by sorry
