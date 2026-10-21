-- Prove2me | Theorems.Thm_DerivativeChainPrivate_normalized_fifth_decic_step
-- name    : DerivativeChainPrivate.normalized_fifth_decic_step
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-20T22:41:36.092352+00:00
-- url     : https://prove2.me/theorems/a4740179-db2f-4ff2-bfec-f2d83ee1e446
-- title:
--   Compatible nonic-to-decic step for a cubic fifth power
-- statement:
--   Let $q_\beta(z)=z^3-z-\beta$ with $\operatorname{Re}\beta\ge0$ and $\operatorname{Im}\beta>0$, and let $P_j$ be the monic normalization of $D^{15-j}(q_\beta^5)$. For an inverse representation $\beta/w=\alpha w^2-b+e/w$, write $A=\operatorname{Re}e/\operatorname{Re}w$, $B=\operatorname{Im}e/\operatorname{Im}w$, and $C=(3A-B)/2$.
--   Suppose $w$ is an actual root of $P_9$ with positive coordinates, $(\operatorname{Re}w)^2\ge4/5$, and an inverse representation with supplied $\alpha_0,b_0,E_0$. Assume
--   $$\frac{7343}{5000}<\alpha_0<\frac{14687}{10000},\quad\frac{12919}{10000}<b_0<\frac{323}{250},$$
--   $A_0\le1/16$, $B_0\le0$, $C_0\le1/8$, and $(\operatorname{Re}w)^2-3(\operatorname{Im}w)^2\ge4/5$.
--   There exist an actual root $z$ of $P_{10}$, real $\alpha,b$ and complex $e$ with nondecreasing real and imaginary coordinates and
--   $$\frac\beta z=\alpha z^2-b+\frac ez,\quad\frac{1461}{1250}<\alpha<\frac{11689}{10000},\quad\frac{2229}{2000}<b<\frac{5573}{5000}.$$
--   At $z$, the corrections satisfy $A\le3/100$, $B\le0$ and $C\le3/50$.
-- source:
--   https://gist.github.com/Amal-David/adce933460b7501cb123f483f62775eb/f5a76eda649f3e995a8ec6b98387b23b64c6debb#file-fifth-md; upper/H5_UPPER_BRIDGE.md, ninth-to-tenth-row bridge and row-10 inverse cubic.

import Definitions.Def_DerivativeChainPrivate_fifth_power_inverse_certificates
import Definitions.Def_DerivativeChainPrivate_fifth_row10_coefficient_bounds
import Definitions.Def_DerivativeChainPrivate_fifth_row10_newton_polynomials
import Mathlib
import Theorems.Thm_DerivativeChainPrivate_row10_complete_inverse_branches
open Polynomial MeasureTheory Filter Set DerivativeChainPrivate
open scoped Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem DerivativeChainPrivate.normalized_fifth_decic_step (β w E₀ : ℂ) (α₀ b₀ : ℝ) (hR : 0 ≤ β.re) (hI : 0 < β.im)
    (hwpos : 0 < w.re) (hwim : 0 < w.im) (hwX : 4/5 ≤ w.re^2)
    (hwroot : (fifthUnitP9 β).eval w=0)
    (hα₀lo : 7343/5000 < α₀) (hα₀up : α₀ < 14687/10000)
    (hb₀lo : 12919/10000 < b₀) (hb₀up : b₀ < 323/250)
    (hwinv : β/w=(α₀:ℂ)*w^2-(b₀:ℂ)+E₀/w)
    (hA₀ : E₀.re/w.re ≤ 1/16) (hB₀ : E₀.im/w.im ≤ 0)
    (hC₀ : (3*(E₀.re/w.re)-E₀.im/w.im)/2 ≤ 1/8)
    (hW₀ : 4/5 ≤ w.re^2-3*w.im^2) :
    ∃ z : ℂ, ∃ α b : ℝ, ∃ e : ℂ,
      (fifthUnitP10 β).eval z=0 ∧ w.re ≤ z.re ∧ w.im ≤ z.im ∧
      1461/1250 < α ∧ α < 11689/10000 ∧ 2229/2000 < b ∧ b < 5573/5000 ∧
      β/z=(α:ℂ)*z^2-(b:ℂ)+e/z ∧ e.re/z.re ≤ 3/100 ∧ e.im/z.im ≤ 0 ∧
      (3*(e.re/z.re)-e.im/z.im)/2 ≤ 3/50 := by sorry
