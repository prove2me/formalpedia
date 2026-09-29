-- Prove2me | Theorems.Thm_AlgebraicCurve_weilDualityAdelic_of_isAlgClosed
-- name    : AlgebraicCurve.weilDualityAdelic_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/c3739bd6-5f0a-590c-91c9-7b991a50d3c6
-- title:
--   Adelic Weil duality over an algebraically closed constant field
-- statement:
--   Let $K$ be an algebraically closed field and $F$ a field equipped with a $K$-algebra structure, subject to the following hypotheses. First, the divisor-theoretic data on $F/K$: `HasCanonicalDivisor` for $F/K$, i.e. every nonzero differential $\omega \in \Omega_{F/K}$ admits a divisor (a finitely supported integer-valued function on places) whose value at each place $v$ is $v.\mathrm{ordDifferential}\,\omega$; `HasPrincipalDivisors` for $F/K$, i.e. every $f \neq 0$ has a degree-zero divisor with values $v.\mathrm{ord}\,f$; `DCoordGenerates` at every place $w$ of $F/K$, i.e. $w.\mathrm{dCoord}$ spans the relevant $F$-module; `FiniteResidue` at every place, i.e. each residue field is finite over $K$; and $\Omega_{F/K}$ nontrivial. Second, `IsCurveOver K F`, i.e. principal divisors exist with degree zero, all residue fields are finite over $K$, and $\Omega_{F/K}$ is free of rank one over $F$; likewise `IsCurveOver K (RatFunc K)`, together with finiteness of residue fields, `DCoordGenerates` at all places, and nontriviality of $\Omega_{K(x)/K}$ for the rational function field. Third, a presentation of $F$ over the rational function field: a $K(x)$-algebra structure on $F$ compatible with $K$, integral, module-finite, finite-dimensional and separable. Fourth, the residue data: `HasLocalResidue K F`, i.e. each place carries a $K$-linear map $F \to$ residue field vanishing on the valuation subring and sending $f$ with $\pi f$ integral to the residue class of $\pi f$; `HasCanonicalLocalResidueKStar K F`, providing a canonical local residue datum over $K$ at every place; and `HasSeparableResidue K F`, i.e. the trace form $\mathrm{Tr}_{K}$ of each residue field is a nonzero $K$-linear map. Then `WeilDualityAdelic K F` holds: for any instances of `IsCurveOver K F`, `HasCanonicalDivisor` and `DCoordGenerates` at all places, and for every nonzero $\omega \in \Omega_{F/K}$ and every divisor $D$, the index of specialty of $D$ — the $K$-dimension of the adele space modulo the sum of the bounded adeles attached to $D$ and the image of the global subspace — equals, as an integer, the invariant `ell` of the divisor $(\omega) - D$, where $(\omega)$ is the canonical divisor attached to $\omega$.
--
--   This is the dimension form of Serre–Weil duality for a function field of one variable over an algebraically closed constant field, $i(D) = \ell((\omega) - D)$. It is used in the modular-curve part of the development, where it supports the computation of the degree of a canonical divisor as $2g - 2$ and the identification of the genus of the modular function field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_weilDualityAdelic_of_isAlgClosed.lean

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

theorem AlgebraicCurve.weilDualityAdelic_of_isAlgClosed
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
    AlgebraicCurve.WeilDualityAdelic K F := by sorry
