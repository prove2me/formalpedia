-- Prove2me | Theorems.Thm_AlgebraicCurve_residueTheorem_of_perfectField
-- name    : AlgebraicCurve.residueTheorem_of_perfectField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/74f51660-0195-531a-8d8c-2a4107a0c8a1
-- title:
--   Residue theorem over a perfect constant field
-- statement:
--   Let $K$ be a perfect field with decidable equality on $\mathrm{RatFunc}\,K$, and let $F$ be a field and $K$-algebra. Assume: every nonzero $\omega\in\Omega[F\!\restriction\! K]$ admits a divisor $D$ (a finitely supported integer-valued function on the places $v$ of $F/K$) with $D(v)=v.\mathrm{ordDifferential}\,\omega=v.\mathrm{ord}(v.\mathrm{differentialCoeff}\,\omega)$ for all $v$; for each place $w$ of $F/K$ the differential $d(\pi_w)$ of a uniformizer spans $\Omega[F\!\restriction\! K]$ over $F$; $F$ is an algebra over $\mathrm{RatFunc}\,K$ compatibly with $K$, integral, module-finite and separable over it; each place of $F/K$ and each place of $\mathrm{RatFunc}\,K$ over $K$ has residue field finite over $K$; $\Omega[F\!\restriction\! K]$ and $\Omega[\mathrm{RatFunc}\,K\!\restriction\! K]$ are nontrivial; $K$-rational functions on $F$ and on $\mathrm{RatFunc}\,K$ have principal divisors of degree $0$, and both $F/K$ and $\mathrm{RatFunc}\,K/K$ satisfy `IsCurveOver` (principal divisors, finite residue fields, and $\Omega$ free of rank one); finally $\mathrm{RatFunc}\,K$ also has canonical divisors and uniformizer-generated differentials at all its places. Then [`AlgebraicCurve.ResidueTheorem K F`](def/AlgebraicCurve_WeilOfKaehler.html#L107) holds: for every nonzero $\omega\in\Omega[F\!\restriction\! K]$ and every $f\in F$, the $K$-linear adelic functional `weilOfKaehler` attached to $\omega$, namely $\alpha\mapsto\sum_v \mathrm{kaehlerResidueTerm}\,\omega\,\alpha\,v$, vanishes at the diagonal adèle of $f$.
--
--   This is the residue theorem for an algebraic function field of one variable over a perfect constant field: the sum over all places of the traced local residues of $f\,\omega$ is zero, phrased as the vanishing on the diagonal copy of $F$ of the Weil functional on adèles built from a nonzero Kähler differential. It is the input for the residue theorem in the smooth relative-dimension-one setting, [`AlgebraicCurve.residueTheorem_functionField_of_smoothOfRelativeDimension_one`](thm.html#AlgebraicCurve.residueTheorem_functionField_of_smoothOfRelativeDimension_one), and thereby for the duality underlying the Riemann–Roch package.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_residueTheorem_of_perfectField.lean

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
import Definitions.Def_AlgebraicCurve_WeilOfKaehler
import Definitions.Def_AlgebraicCurve_TateResidueCurrency
import Definitions.Def_AlgebraicCurve_CanonicalLocalResidueInstanceV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.residueTheorem_of_perfectField
    {K F : Type*} [Field K] [PerfectField K] [DecidableEq (RatFunc K)]
    [Field F] [Algebra K F]
    [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F)]
    [∀ w : AlgebraicCurve.Place K F, w.DCoordGenerates]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [Algebra.IsIntegral (RatFunc K) F] [Module.Finite (RatFunc K) F]
    [∀ w : AlgebraicCurve.Place K F, w.FiniteResidue]
    [Nontrivial Ω[F⁄K]]
    [AlgebraicCurve.IsCurveOver K F] [AlgebraicCurve.IsCurveOver K (RatFunc K)]
    [∀ u : AlgebraicCurve.Place K (RatFunc K), u.FiniteResidue]
    [AlgebraicCurve.HasPrincipalDivisors K F] [Algebra.IsSeparable (RatFunc K) F]
    [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := RatFunc K)]
    [Nontrivial Ω[(RatFunc K)⁄K]] [∀ v : AlgebraicCurve.Place K (RatFunc K), v.DCoordGenerates] :
    AlgebraicCurve.ResidueTheorem K F := by sorry
