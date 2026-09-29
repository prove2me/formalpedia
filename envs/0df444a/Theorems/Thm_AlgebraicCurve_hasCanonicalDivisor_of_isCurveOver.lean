-- Prove2me | Theorems.Thm_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver
-- name    : AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/84375f49-6cc7-5c4e-b9b7-b80767fb5a0d
-- title:
--   Existence of canonical divisors on a curve over a perfect field
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, assume $K$ is perfect, that $F$ is essentially of finite type over $K$, and that [`AlgebraicCurve.IsCurveOver K F`](def/AlgebraicCurve_IsCurveOver.html#L15) holds; the latter says three things: (i) principal divisors exist, i.e. for every $f \in F^{\times}$ there is a finitely supported function $D \colon \mathrm{Place}\,K\,F \to \mathbb{Z}$ with $D(v) = \mathrm{ord}_v(f)$ at every place $v$ and $\deg D = 0$, where a place of $F/K$ is a valuation subring of $F$ containing the image of $K$, different from $F$ itself, and a principal ideal ring; (ii) for every place $v$ the residue field of that valuation subring is a finite-dimensional $K$-module; and (iii) the module of Kähler differentials $\Omega_{F/K}$ is free of rank one over $F$. The conclusion is [`AlgebraicCurve.HasCanonicalDivisor`](def/AlgebraicCurve_CanonicalDivisor.html#L14): for every $\omega \in \Omega_{F/K}$ with $\omega \neq 0$ there is a finitely supported divisor $D \colon \mathrm{Place}\,K\,F \to_{f} \mathbb{Z}$ such that, for every place $v$, $D(v)$ equals $\mathrm{ord}_v$ of the coefficient of $\omega$ read off against the local differential at $v$, that is $D(v) = v.\mathrm{ordDifferential}(\omega)$.
--
--   This is the existence of canonical divisors on a curve: the local orders of a nonzero differential vanish at all but finitely many places, so a differential determines a divisor class. It is the hypothesis under which Riemann–Roch theory for $\Omega_{F/K}$ is developed in this formalisation, and it is invoked generically for every curve over a perfect base, including the function fields of the modular curves $X_0(N)$ used later.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CanonicalDivisor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    [PerfectField K] [Algebra.EssFiniteType K F] [AlgebraicCurve.IsCurveOver K F] :
    AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F) := by sorry
