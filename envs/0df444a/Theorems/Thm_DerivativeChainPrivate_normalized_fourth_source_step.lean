-- Prove2me | Theorems.Thm_DerivativeChainPrivate_normalized_fourth_source_step
-- name    : DerivativeChainPrivate.normalized_fourth_source_step
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-20T15:48:06.788951+00:00
-- url     : https://prove2.me/theorems/05361782-4944-4ca7-a428-bd51c00d5a11
-- title:
--   Selected octic root extends to a source root of a cubic fourth power
-- statement:
--   Let $\operatorname{Re}\beta\ge0$ and $\operatorname{Im}\beta>0$, and let $w$ be an actual monic eighth-row root of $(z^3-\frac{11}{2}z-55\beta)^4$. Assume that $w$ has positive real and imaginary parts, $(\operatorname{Re}w)^2\ge4$, and the selected inverse identity
--   $$\frac{\beta}{w}=\frac{28-3\sqrt{26}}{550}w^2-\frac{1274-99\sqrt{26}}{6500}+\frac{R_8(w)}{w},$$
--   where $R_8$ is the imported octic remainder. Then there exists a root $\rho$ of the original cubic such that
--   $$\rho^3-\frac{11}{2}\rho-55\beta=0,\qquad
--   \operatorname{Re}w\le\operatorname{Re}\rho,\qquad
--   \operatorname{Im}w\le\operatorname{Im}\rho.$$
--   This supplies the source endpoint for the fourth-power chain. Repeating that endpoint in the last four rows is justified separately by inheritance of source roots under derivatives of a power.
-- source:
--   https://gist.github.com/Amal-David/adce933460b7501cb123f483f62775eb (revision f5a76eda649f3e995a8ec6b98387b23b64c6debb); cone/OCTIC_H4_INVERSE_MEASURE.md, final source-step argument; complex/H4_COMPLETE_CHAIN.md, source suffix.

import Definitions.Def_DerivativeChainPrivate_higher_power_radicals
import Mathlib
open Polynomial MeasureTheory Filter Set DerivativeChainPrivate
open scoped Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

theorem DerivativeChainPrivate.normalized_fourth_source_step (β w : ℂ) (hR : 0 ≤ β.re) (hI : 0 < β.im)
    (hwpos : 0 < w.re) (hwim : 0 < w.im) (hwX : 4 ≤ w.re^2)
    (hwroot : w^8-(28/3)*w^6-56*β*w^5+(77/3)*w^4+(770/3)*β*w^3-(121/6)*w^2+
      550*β^2*w^2-(605/3)*β*w+1331/720-(1210/3)*β^2=0)
    (hwinv : β/w = (((28-3*Real.sqrt 26)/550:ℝ):ℂ)*w^2-(((1274-99*Real.sqrt 26)/6500:ℝ):ℂ)+octicRemainder w/w) :
    ∃ z : ℂ, z^3-(11/2)*z-55*β=0 ∧ w.re ≤ z.re ∧ w.im ≤ z.im := by sorry
