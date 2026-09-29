-- Prove2me | Theorems.Thm_AlgebraicCurve_existsUnique_hasSimpleResidue_of_hasSimplePoleAt
-- name    : AlgebraicCurve.existsUnique_hasSimpleResidue_of_hasSimplePoleAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/2559b2d2-89be-5bcc-afa4-7d584ad0e9be
-- title:
--   Unique residue at a place with at most a simple pole
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, $K$ algebraically closed and $F$ essentially of finite type over $K$, and assume $F$ is a curve over $K$ in the project's sense: every nonzero $f \in F$ has a divisor $D$ with $D(v) = \operatorname{ord}_v f$ at every place and $\deg D = 0$, each residue field $\kappa(v)$ is a finite $K$-module, and $\Omega_{F/K}$ is free of rank $1$ over $F$; assume also that every nonzero $\omega \in \Omega_{F/K}$ admits a divisor $D$ with $D(v) = \operatorname{ord}_v(\omega)$ for all $v$. Here a place $v$ is a valuation subring $\mathcal{O}_v \subsetneq F$ containing $\operatorname{im}(K \to F)$ and which is a principal ideal ring; $\pi_v$ denotes its chosen irreducible element and $d\pi_v \in \Omega_{F/K}$ its differential. Let $v$ be a place and $\omega \in \Omega_{F/K}$, and suppose $\omega$ has at most a simple pole at $v$, that is, $\omega = f \cdot d\pi_v$ for some $f \in F$ with $\pi_v f \in \mathcal{O}_v$. Then there is exactly one $a \in K$ such that $\omega = f' \cdot d\pi_v$ for some $f' \in F$ with $\pi_v f' \in \mathcal{O}_v$ whose residue class in $\kappa(v)$ is the image of $a$.
--
--   This is the well-definedness of the residue at a place of a differential with at most a simple pole, in the form needed to treat "$\omega$ has residue $a$ at $v$" as a function of $\omega$ and $v$. It underlies the construction of the space of differentials with at most simple poles on a finite set of places and the residue map on it, and is used in the residue computations for differentials on modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_existsUnique_hasSimpleResidue_of_hasSimplePoleAt.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_PolarDifferentials

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.existsUnique_hasSimpleResidue_of_hasSimplePoleAt
    {K F : Type*} [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [Algebra.EssFiniteType K F]
    [AlgebraicCurve.IsCurveOver K F] [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F)]
    (v : AlgebraicCurve.Place K F) (ω : Ω[F⁄K]) (hω : v.HasSimplePoleAt ω) :
    ∃! a : K, v.HasSimpleResidue ω a := by sorry
