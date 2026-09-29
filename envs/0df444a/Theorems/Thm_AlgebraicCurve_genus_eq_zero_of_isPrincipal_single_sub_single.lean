-- Prove2me | Theorems.Thm_AlgebraicCurve_genus_eq_zero_of_isPrincipal_single_sub_single
-- name    : AlgebraicCurve.genus_eq_zero_of_isPrincipal_single_sub_single
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/7d93c674-9432-58ac-9f9f-9f3b963b2256
-- title:
--   A principal divisor P-Q with deg Q=1 forces genus zero
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and assume $F$ is a curve over $K$ in the sense of `IsCurveOver`: every nonzero $f \in F$ has an associated divisor whose coefficient at each place $v$ is $v.\mathrm{ord}\,f$ and whose degree is $0$, each residue field $v.\mathrm{ResidueField}$ is finite-dimensional over $K$, and $\Omega_{F/K}$ is free of rank one over $F$. Assume also `HasCanonicalDivisor`, i.e. every nonzero $\omega \in \Omega_{F/K}$ admits a divisor with coefficients $v.\mathrm{ordDifferential}\,\omega$, and that for every place $v$ the differential $d(\pi_v)$ of a uniformizer spans $\Omega_{F/K}$ over $F$. Two further hypotheses are assumed: Riemann–Roch for $F/K$, namely $\ell(D) - \ell(K_F - D) = \deg D + 1 - g$ for every divisor $D$ and every canonical divisor $K_F$ attached to a nonzero differential; and that the constants are the base field, i.e. the Riemann–Roch space $L(0)$ equals the image of $K$ in $F$. Finally, let $P \neq Q$ be places with $\deg Q = \dim_K Q.\mathrm{ResidueField} = 1$, and suppose the divisor $P - Q$ is principal: there is $f \in F$, $f \neq 0$, with $\mathrm{ord}_P f = 1$, $\mathrm{ord}_Q f = -1$ and $\mathrm{ord}_v f = 0$ at all other places. Then the genus of $F/K$, defined as $\lfloor (\deg K_F + 2)/2 \rfloor$ (truncated to $\mathbb{N}$) for a canonical divisor $K_F$, is $0$.
--
--   This is the classical criterion for a function field to be rational: a curve carrying a function with a single simple zero and a single simple pole at a place of degree one has genus zero. It is used in the study of the cuspidal divisor class on modular curves, in particular in the proof that the cuspidal class is nonzero and in the comparison of specialisations of degree-zero divisor classes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_genus_eq_zero_of_isPrincipal_single_sub_single.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_CanonicalDivisor
import Definitions.Def_ModularCurve_CanonicalDivisorUniformizer
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_RiemannRochRows

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicCurve

theorem genus_eq_zero_of_isPrincipal_single_sub_single {K : Type*} {F : Type*} [Field K] [Field F] [Algebra K F]
    [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]
    (hRR : FunctionFieldRiemannRoch K F) (hC : ConstantsAreBase K F)
    {P Q : Place K F} (hPQ : P ≠ Q) (hQ : Q.deg = 1)
    (h : Divisor.IsPrincipal (Finsupp.single P 1 - Finsupp.single Q 1)) :
    genus K F = 0 := by sorry
