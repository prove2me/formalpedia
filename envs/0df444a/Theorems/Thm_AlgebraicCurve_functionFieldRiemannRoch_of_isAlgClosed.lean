-- Prove2me | Theorems.Thm_AlgebraicCurve_functionFieldRiemannRoch_of_isAlgClosed
-- name    : AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/b4ac021e-cbea-59f4-abb3-092663a1778d
-- title:
--   Riemann–Roch over an algebraically closed base field
-- statement:
--   Let $K$ be an algebraically closed field (no restriction on characteristic), with decidable equality on $\mathrm{RatFunc}\,K$, and let $F$ be a field and a $K$-algebra which is moreover an algebra over $\mathrm{RatFunc}\,K$ compatibly with $K$ (scalar tower), integral, module-finite and finite-dimensional over $\mathrm{RatFunc}\,K$, and separable over it. Assume: `HasCanonicalDivisor`, i.e. for every nonzero $\omega \in \Omega_{F/K}$ the function $v \mapsto v.\mathrm{ordDifferential}\,\omega$ on places is given by a finitely supported divisor; at every place of $F$ and of $\mathrm{RatFunc}\,K$ the element `dCoord` spans $\Omega$ over the field (`DCoordGenerates`) and the residue field is finite-dimensional over $K$ (`FiniteResidue`); $\Omega_{F/K}$ and $\Omega_{\mathrm{RatFunc}\,K/K}$ are nontrivial; `HasLocalResidue K F`, i.e. every place carries a $K$-linear residue map on $F$ vanishing on the valuation subring and sending $f$ with $\pi f$ integral to the residue class of $\pi f$; `HasCanonicalLocalResidueKStar K F`, a choice of canonical local residue datum over $K$ at each place; `HasPrincipalDivisors K F`, i.e. each nonzero $f \in F$ has a divisor of valuations of total degree $0$; `IsCurveOver K F` and $\mathrm{IsCurveOver}\,K\,(\mathrm{RatFunc}\,K)$ (principal divisors, finite residue fields, $\Omega$ free of rank one); and `HasSeparableResidue K F`, i.e. the trace form $\mathrm{Tr}_{\kappa(v)/K}$ is nonzero at every place. Then `FunctionFieldRiemannRoch K F` holds: granted the curve, canonical-divisor and `DCoordGenerates` structures, for every nonzero $\omega \in \Omega_{F/K}$ and every divisor $D$ of $F/K$, $\ell(D) - \ell\bigl((\omega) - D\bigr) = \deg D + 1 - g$, with $(\omega)$ the chosen canonical divisor of $\omega$ and $g$ the genus as defined from the degree of a canonical divisor.
--
--   This is the Riemann–Roch theorem for the function field $F/K$ of a curve over an algebraically closed field, in Tate's residue-theoretic formulation. It is the form used downstream to compute $\deg(\omega) = 2g-2$, to identify $\ell((\omega)) = g$, and in the ramification count [`AlgebraicCurve.finsum_ramificationIndexAlong_sub_one_eq`](thm.html#AlgebraicCurve.finsum_ramificationIndexAlong_sub_one_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_functionFieldRiemannRoch_of_isAlgClosed.lean

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

theorem AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed
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
    [FiniteDimensional (RatFunc K) F] [AlgebraicCurve.HasSeparableResidue K F] :
    AlgebraicCurve.FunctionFieldRiemannRoch K F := by sorry
