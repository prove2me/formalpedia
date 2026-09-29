-- Prove2me | Theorems.Thm_AlgebraicCurve_residueTheorem_of_isAlgClosed
-- name    : AlgebraicCurve.residueTheorem_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/7f7229f4-36cb-5d03-a67c-34160f920c00
-- title:
--   Residue theorem for curves over an algebraically closed field
-- statement:
--   Let $K$ be an algebraically closed field and $F$ a field extension of $K$, subject to the following assumptions. The differential module $\Omega[F/K]$ is nontrivial and admits canonical divisors, in the sense that every nonzero $\omega \in \Omega[F/K]$ has a finitely supported $\mathbb{Z}$-valued function $D$ on the places of $F$ over $K$ (valuation subrings of $F$, proper, containing $K$, and principal) with $D v = v.\mathrm{ordDifferential}\,\omega$ for all $v$; for each place $w$ the element $w.\mathrm{dCoord}$ spans $\Omega[F/K]$ over $F$, and each residue field $w.\mathrm{ResidueField}$ is finite over $K$. Every place carries a local residue datum: a $K$-linear map $F \to w.\mathrm{ResidueField}$ vanishing on the valuation subring and sending $f$ with $\varpi_w f$ integral to the residue class of $\varpi_w f$; moreover a distinguished such family is chosen (`HasCanonicalLocalResidueKStar`), each member additionally killing $\varpi_w^{-(n+1)}$ for $n \ge 1$. Further, $F$ is an integral, module-finite, separable extension of $\mathrm{RatFunc}\,K$ compatibly with $K$; every nonzero $f \in F$ has a divisor of degree zero recording its orders; and both $F$ and $\mathrm{RatFunc}\,K$ are curves over $K$ (principal divisors, residue fields finite over $K$, $\Omega$ free of rank one), with $\Omega[\mathrm{RatFunc}\,K/K]$ nontrivial, all its places having finite residue fields and spanning $\mathrm{dCoord}$. Then `ResidueTheorem K F` holds: for every nonzero $\omega \in \Omega[F/K]$ and every $f \in F$, the Weil functional $\mathrm{weilOfKaehler}\,K\,F$ attached to $\omega$ vanishes on the adèle given by the diagonal image of $f$.
--
--   This is the residue theorem for an algebraic function field of one variable over an algebraically closed constant field: the sum of the local residues of $f\,\omega$ over all places is zero, expressed as the vanishing of the Weil functional attached to $\omega$ on principal adèles. It is used in the comparison of Kähler differentials with Weil differentials, and in particular feeds [`AlgebraicCurve.Differential.sum_ord_smul_pullbackAlong_eq_zero`](thm.html#AlgebraicCurve.Differential.sum_ord_smul_pullbackAlong_eq_zero) and the agreement statement for the modular function field over $\mathbb{C}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_residueTheorem_of_isAlgClosed.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.residueTheorem_of_isAlgClosed
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
    [Nontrivial Ω[(RatFunc K)⁄K]] [∀ v : AlgebraicCurve.Place K (RatFunc K), v.DCoordGenerates] :
    AlgebraicCurve.ResidueTheorem K F := by sorry
