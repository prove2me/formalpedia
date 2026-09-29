-- Prove2me | Theorems.Thm_AlgebraicCurve_sumRamificationInertia_of_fundamentalIdentity
-- name    : AlgebraicCurve.sumRamificationInertia_of_fundamentalIdentity
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/8332978f-9d48-5563-bc0b-aa421ab5f9f0
-- title:
--   Relative ramification–inertia identity from the degree identity
-- statement:
--   Let $K$, $F$, $F'$ be fields with $F$ and $F'$ algebras over $K$ and $F'$ an algebra over $F$, the three structures forming a scalar tower over $K$, and with $F'$ integral over $F$. Here a place of $F$ over $K$ is a valuation subring of $F$ containing the image of $K$, different from all of $F$, and whose ideals are principal; its degree is the $K$-dimension of its residue field, for a place $w$ of $F'$ the restricted place $w|_F$ is the contraction of the valuation subring along $F \to F'$, the fibre of a place $v$ of $F$ consists of the places $w$ of $F'$ with $w|_F = v$, the ramification index $e(w/F)$ is the least positive $n$ occurring as $w.\mathrm{ord}$ of the image of some nonzero element of $F$, and the inertia degree $f(w/F)$ is the dimension of the residue field of $w$ over that of $w|_F$. Assume `HasPrincipalDivisors K F'` (every nonzero $f \in F'$ has a finitely supported divisor whose value at each place $v$ is $v.\mathrm{ord}\,f$ and whose degree is $0$), assume the identity $\sum_{w \mid v} e(w/F)\deg(w) = [F':F]\deg(v)$ for every place $v$ of $F$ over $K$, and assume $\deg(v) \neq 0$ for every such $v$. Then $\sum_{w \mid v} e(w/F) f(w/F) = [F':F]$ for every place $v$ of $F$ over $K$.
--
--   This is the passage from the degree-weighted form of the fundamental identity of ramification theory for the extension $F'/F$ of function fields over $K$ to its relative form $\sum_{w \mid v} e(w/v) f(w/v) = [F':F]$, valid once no place of $F$ over $K$ has degree zero. It supplies the `SumRamificationInertia` instance used in the divisor push–pull formalism, and is invoked in the comparison of divisor correspondences and in the study of Tate modules of Jacobians of modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_sumRamificationInertia_of_fundamentalIdentity.lean

import Definitions.Def_AlgebraicCurve_DivisorPushPull

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.sumRamificationInertia_of_fundamentalIdentity
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F']
    [IsScalarTower K F F'] [Algebra.IsIntegral F F'] [HasPrincipalDivisors K F']
    [FundamentalIdentity K F F']
    (hdeg : ∀ v : Place K F, v.deg ≠ 0) : SumRamificationInertia K F F' := by sorry
