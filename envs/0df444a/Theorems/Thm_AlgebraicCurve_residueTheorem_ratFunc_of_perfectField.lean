-- Prove2me | Theorems.Thm_AlgebraicCurve_residueTheorem_ratFunc_of_perfectField
-- name    : AlgebraicCurve.residueTheorem_ratFunc_of_perfectField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/f0d4d3e0-da0e-5903-8a02-c56794377e8a
-- title:
--   Residue theorem for K(x) over a perfect field
-- statement:
--   Let $K$ be a perfect field and let $F = \mathrm{RatFunc}\,K$ be the rational function field over $K$, subject to the following hypotheses: $F$ is a curve over $K$ in the sense of [`AlgebraicCurve.IsCurveOver`](def/AlgebraicCurve_IsCurveOver.html#L15), that is, every nonzero $f \in F$ has a divisor of degree $0$ whose value at each place $v$ is $v.\mathrm{ord}\,f$, every place has residue field finite as a $K$-module, and $\Omega[F/K]$ is free of rank $1$ over $F$; the class `HasCanonicalDivisor` holds, i.e. every nonzero $\omega \in \Omega[F/K]$ admits a divisor $D$ with $D(v) = v.\mathrm{ord}(v.\mathrm{differentialCoeff}\,\omega)$ at every place $v$; every place $v$ satisfies `DCoordGenerates`, i.e. $\mathrm{d}$ of a uniformiser at $v$ spans $\Omega[F/K]$ over $F$; and $\Omega[F/K]$ is nontrivial. Here a place is a valuation subring of $F$, proper, containing the image of $K$, and a principal ideal ring. The conclusion is [`AlgebraicCurve.ResidueTheorem K (RatFunc K)`](def/AlgebraicCurve_WeilOfKaehler.html#L107): for every nonzero $\omega \in \Omega[F/K]$ and every $f \in F$, the $K$-linear functional `weilOfKaehler` attached to $\omega$, which sends an adele $\alpha$ to the finite sum over all places $v$ of the local terms `kaehlerResidueTerm` $\omega\,\alpha\,v$, vanishes on the diagonal adele of $f$.
--
--   This is the residue theorem for the projective line, i.e. the genus-zero case of the statement that the sum over all places of the local residue traces of $f\,\omega$ vanishes, as in Tate's treatment of differentials and Riemann–Roch on curves. It is the base case from which [`AlgebraicCurve.residueTheorem_of_perfectField`](thm.html#AlgebraicCurve.residueTheorem_of_perfectField) obtains the residue theorem for a general curve over a perfect field, and its proof rests on the computation of the local traced residues at the finite places and at infinity for $c/p^m$ and for powers of $x$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_residueTheorem_ratFunc_of_perfectField.lean

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

theorem AlgebraicCurve.residueTheorem_ratFunc_of_perfectField
    (K : Type*) [Field K] [PerfectField K] [DecidableEq (RatFunc K)]
    [AlgebraicCurve.IsCurveOver K (RatFunc K)]
    [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := RatFunc K)]
    [∀ v : AlgebraicCurve.Place K (RatFunc K), v.DCoordGenerates]
    [Nontrivial Ω[(RatFunc K)⁄K]] :
    AlgebraicCurve.ResidueTheorem K (RatFunc K) := by sorry
