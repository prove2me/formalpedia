-- Prove2me | Theorems.Thm_DerivativeChainPrivate_normalized_cube_quintic_step
-- name    : DerivativeChainPrivate.normalized_cube_quintic_step
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T04:05:53.271982+00:00
-- url     : https://prove2.me/theorems/aee373d9-7de5-4f0d-a039-ba274017d9f7
-- title:
--   A northeast quintic parent with its exact inverse
-- statement:
--   Let $\beta\in\mathbb C$ satisfy $\operatorname{Re}\beta,\operatorname{Im}\beta\ge0$. Put $Q_3(z)=z^3-z-\beta$, $Q_4(z)=z^4-2z^2-4\beta z+8/21$, $Q_5(z)=z^5-(10/3)z^3-10\beta z^2+(40/21)z+(16/3)\beta$, and $Q_6(z)=z^6-5z^4-20\beta z^3+(40/7)z^2+32\beta z-16/21+28\beta^2$. Let $\operatorname{Re}w>0$, $\operatorname{Im}w\ge0$, $(\operatorname{Re}w)^2\ge7/4$, $Q_4(w)=0$, and $\beta/w=w^2/4-1/2+(2/21)/w^2$. There exists $z$ with $Q_5(z)=0$, both coordinates at least those of $w$, $(\operatorname{Re}z)^2\ge5/2$, and
--
--   $$\beta/z=z^2/10-7/25+(36/875)/(z^2-8/15).$$
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Dependencies/VerifiedCube.lean#L904-L1035

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate Polynomial MeasureTheory Filter Set Topology Metric Function ComplexConjugate
open scoped BigOperators ComplexOrder Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem DerivativeChainPrivate.normalized_cube_quintic_step (β w : ℂ)
    (hR : 0 ≤ β.re) (hI : 0 ≤ β.im) (hwpos : 0 < w.re) (hwim : 0 ≤ w.im)
    (hwX : 7/4 ≤ w.re ^ 2)
    (hwroot : w ^ 4 - 2 * w ^ 2 - 4 * β * w + 8/21 = 0)
    (hwinv : β / w = (1/4 : ℂ) * w ^ 2 - 1/2 + (2/21 : ℂ) / w ^ 2) :
    ∃ z : ℂ,
      z ^ 5 - 10/3 * z ^ 3 - 10 * β * z ^ 2 + 40/21 * z + 16/3 * β = 0 ∧
      w.re ≤ z.re ∧ w.im ≤ z.im ∧ 5/2 ≤ z.re ^ 2 ∧
      β / z = (1/10 : ℂ) * z ^ 2 - 7/25 + (36/875 : ℂ) / (z ^ 2 - 8/15) := by sorry
