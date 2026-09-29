-- Prove2me | Theorems.Thm_AlgebraicCurve_degree_canonicalDivisor_eq_of_isAlgClosed
-- name    : AlgebraicCurve.degree_canonicalDivisor_eq_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/1628ca08-ae66-54fc-a113-0bb819e7c43f
-- title:
--   Degree of a canonical divisor is 2g-2 over ̄ K
-- statement:
--   Let $K$ be an algebraically closed field and $F$ a field extension of $K$ which is an algebraic function field in the sense encoded by the ambient hypotheses: $F$ is an $K$-algebra which is also an algebra over $\mathrm{RatFunc}\,K$ compatibly with $K$ (scalar tower), integral, module-finite and finite-dimensional over $\mathrm{RatFunc}\,K$ and separable over it; the modules $\Omega[F/K]$ and $\Omega[\mathrm{RatFunc}\,K / K]$ are nontrivial; both $F$ and $\mathrm{RatFunc}\,K$ are curves over $K$, meaning every nonzero function has a divisor of its orders of degree $0$, all residue fields of places are finite over $K$, and the differentials are free of rank one over the function field; at every place of $F$ and of $\mathrm{RatFunc}\,K$ the element $v.\mathrm{dCoord}$ spans the differentials over the function field and the residue field is finite over $K$; every place of $F$ carries local residue data, there is a chosen canonical such datum at each place of $F$ (killing $\pi^{-(n+1)}$ for $n\ge 1$), the trace $\mathrm{Algebra.trace}\,K\,v.\mathrm{ResidueField}$ is a nonzero $K$-linear map at every place, and every nonzero differential has an associated divisor of its orders of vanishing. Then for every nonzero $\omega \in \Omega[F/K]$ the divisor `canonicalDivisorOf hω`, whose value at a place $v$ is $v.\mathrm{ordDifferential}\,\omega$, has degree $\sum_v \mathrm{ord}_v(\omega)\deg v = 2g - 2$, where $g$ is [`AlgebraicCurve.genus K F`](def/AlgebraicCurve_CanonicalDivisor.html#L33), defined as $(\deg(\text{a canonical divisor})+2)/2$.
--
--   This is the classical identity $\deg(K_F) = 2g-2$ for the canonical class of a curve over an algebraically closed base field, with the genus taken in its canonical-degree normalisation. It is used in the genus computations for modular function fields, notably in the Riemann–Hurwitz style count of ramification contributions and in the canonical-divisor degree formulas for modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_degree_canonicalDivisor_eq_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_CanonicalDivisor
import Definitions.Def_ModularCurve_CanonicalDivisorUniformizer
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_LocalResidue
import Definitions.Def_AlgebraicCurve_RiemannRochRows

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.degree_canonicalDivisor_eq_of_isAlgClosed
    {K F : Type*} [Field K] [IsAlgClosed K] [DecidableEq (RatFunc K)]
    [Field F] [Algebra K F]
    [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F)]
    [∀ w : AlgebraicCurve.Place K F, w.DCoordGenerates]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [Algebra.IsIntegral (RatFunc K) F] [Module.Finite (RatFunc K) F]
    [AlgebraicCurve.HasLocalResidue K F]
    [∀ w : AlgebraicCurve.Place K F, w.FiniteResidue]
    [Nontrivial Ω[F⁄K]]
    [AlgebraicCurve.IsCurveOver K F] [AlgebraicCurve.IsCurveOver K (RatFunc K)]
    [∀ u : AlgebraicCurve.Place K (RatFunc K), u.FiniteResidue]
    [AlgebraicCurve.HasCanonicalLocalResidueKStar K F]
    [AlgebraicCurve.HasPrincipalDivisors K F] [Algebra.IsSeparable (RatFunc K) F]
    [Nontrivial Ω[(RatFunc K)⁄K]] [∀ v : AlgebraicCurve.Place K (RatFunc K), v.DCoordGenerates]
    [FiniteDimensional (RatFunc K) F] [AlgebraicCurve.HasSeparableResidue K F]
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) :
    AlgebraicCurve.Divisor.degree (AlgebraicCurve.canonicalDivisorOf hω) = 2 * (AlgebraicCurve.genus K F : ℤ) - 2 := by sorry
