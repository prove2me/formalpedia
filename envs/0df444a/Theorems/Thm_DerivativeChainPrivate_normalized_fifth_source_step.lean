-- Prove2me | Theorems.Thm_DerivativeChainPrivate_normalized_fifth_source_step
-- name    : DerivativeChainPrivate.normalized_fifth_source_step
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-20T18:50:53.501072+00:00
-- url     : https://prove2.me/theorems/598f4f0e-08ee-4dc0-b7ce-e33ff7c2f366
-- title:
--   Compatible tenth-row-to-source-root step for a cubic fifth power
-- statement:
--   Let $q_\beta(z)=z^3-z-\beta$ with $\operatorname{Re}\beta\ge0$ and $\operatorname{Im}\beta>0$, and let $P_j$ be the monic normalization of $D^{15-j}(q_\beta^5)$. For an inverse representation $\beta/w=\alpha w^2-b+e/w$, write $A=\operatorname{Re}e/\operatorname{Re}w$, $B=\operatorname{Im}e/\operatorname{Im}w$, and $C=(3A-B)/2$.
--   Suppose $w$ is an actual root of $P_{10}$ with positive real and imaginary parts and a supplied inverse representation satisfying $\alpha>1461/1250$, $b>2229/2000$ and $C\le3/50$.
--   There is a root $z$ of the source cubic itself such that
--   $$z^3-z-\beta=0,\qquad\operatorname{Re}w\le\operatorname{Re}z,\qquad\operatorname{Im}w\le\operatorname{Im}z.$$
--   This root supplies all five final entries of the fifth-power chain, since a source root has multiplicity at least five in $q_\beta^5$.
-- source:
--   https://gist.github.com/Amal-David/adce933460b7501cb123f483f62775eb/f5a76eda649f3e995a8ec6b98387b23b64c6debb#file-fifth-md; H5_COMPLETE_CHAIN.md, final source-root step; upper/H5_UPPER_BRIDGE.md.

import Definitions.Def_DerivativeChainPrivate_fifth_power_inverse_certificates
import Mathlib
open Polynomial MeasureTheory Filter Set DerivativeChainPrivate
open scoped Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem DerivativeChainPrivate.normalized_fifth_source_step (β w e : ℂ) (α b : ℝ) (hR : 0 ≤ β.re) (hI : 0 < β.im)
    (hwpos : 0 < w.re) (hwim : 0 < w.im)
    (hwroot : (fifthUnitP10 β).eval w=0)
    (hαlo : 1461/1250 < α) (hblo : 2229/2000 < b)
    (hwinv : β/w=(α:ℂ)*w^2-(b:ℂ)+e/w)
    (hC : (3*(e.re/w.re)-e.im/w.im)/2 ≤ 3/50) :
    ∃ z : ℂ, z^3-z-β=0 ∧ w.re ≤ z.re ∧ w.im ≤ z.im := by sorry
