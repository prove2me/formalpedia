-- Prove2me | Theorems.Thm_DerivativeChainPrivate_Hermite_hermiteVarianceObstruction
-- name    : DerivativeChainPrivate.Hermite.hermiteVarianceObstruction
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-18T08:19:06.196213+00:00
-- url     : https://prove2.me/theorems/2b2d6580-72f4-44ab-8ccb-989f1aa71e91
-- title:
--   Hermite closed-return square increment exceeds nine variance increments
-- statement:
--   For the probabilists' Hermite polynomials $H_1=x$, $H_2=x^2-1$, $H_3=x^3-3x$, $H_4=x^4-6x^2+3$, $H_5=x^5-10x^3+15x$ and $H_6=x^6-15x^4+45x^2-15$, both $H_5$ and $H_6$ split over the reals and $H_{m+1}'=(m+1)H_m$ for $1\le m\le5$.
--
--   For $m=5,6$, let $B_m$ be the infimum of $\sum_{j=1}^{m-1}|z_{j+1}-z_j|+|z_m|$ over real roots $z_j$ of $H_j$ in every row. Their centroid is zero, so this is the closed-return cost. Let $V_m$ be the uniform variance of the full root multiset of $H_m$, computed about its actual mean. Then $V_5=4$, $V_6=5$, and
--   $$B_6^2-B_5^2>9(V_6-V_5).$$
--   This is an actual Hermite derivative-tower obstruction to universal one-step square-increment coefficients nine and eight. The formal proof uses $B_6\ge93/20$ and $B_5\le2\sqrt3$; it does not assert the sharper exact radical values of both minima. It does not refute a global closed-return inequality or either unrestricted derivative-chain prize question.
-- source:
--   Derivative-zero chains: public formalization reference, R44, DerivativeChainPrivate.Hermite.hermiteVarianceObstruction. https://gist.github.com/Amal-David/d6612109c98595b12561cd638c60edf5/3883c57ddc7bf9d4c0e898c3d6bfd2ca0d7f9c95#file-notes-md

import Mathlib
import Definitions.Def_DerivativeChainPrivate_hermite_closed
open Polynomial DerivativeChainPrivate.Hermite
set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem DerivativeChainPrivate.Hermite.hermiteVarianceObstruction :
    (H 5).Splits ∧ (H 6).Splits ∧
    (∀ m ∈ Finset.Icc 1 5, derivative (H (m+1)) = (m+1 : ℝ) • H m) ∧
    UniformVariance 5 = 4 ∧ UniformVariance 6 = 5 ∧
    9 * (UniformVariance 6 - UniformVariance 5) < Budget 6 ^ 2 - Budget 5 ^ 2:= by sorry
