-- Prove2me | Theorems.Thm_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed
-- name    : AlgebraicCurve.residueTheoremK_ratFunc_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/74e12376-4ca7-54f2-9fc3-7fcedc86b3f2
-- title:
--   Residue theorem for K(x), K algebraically closed
-- statement:
--   Let $K$ be an algebraically closed field, and take $F = \mathrm{RatFunc}\,K$ to be the rational function field over $K$, equipped with decidable equality. Here a place $v$ of $F/K$ is a valuation subring of $F$ containing the image of $K$, different from $F$ itself, and a principal ideal ring. Assume: a chosen family, one for each place $v$, of canonical local residue data at $v$, i.e. local residue data whose functional satisfies $\mathrm{res}\,(\pi_v^{n+1})^{-1} = 0$ for all $n \ge 1$, $\pi_v$ the uniformizer of $v$; that every nonzero $\omega \in \Omega_{F/K}$ admits a finitely supported divisor $D$ on places with $D(v) = v.\mathrm{ordDifferential}\,\omega$, the valuation at $v$ of the differential coefficient of $\omega$, at every $v$; and that at each place $v$ the single differential $d\pi_v$ spans $\Omega_{F/K}$ over $F$. The conclusion is the proposition $\mathrm{ResidueTheoremK}\,K\,(\mathrm{RatFunc}\,K)$: for every family $R = (\mathrm{res}_v)_v$ of canonical local residue data at all places (not merely the chosen one), assuming moreover that every nonzero element of $F$ has a degree-zero divisor recording its valuations, and for every nonzero $\omega \in \Omega_{F/K}$ and every $f \in F$, the Weil functional $\mathrm{weilOfKaehlerK}\,R\,\omega$ on the adele space, given by the (finitely supported) sum over places of the local residue terms of $\omega$, annihilates the adele obtained by embedding $f$ diagonally.
--
--   This is the residue theorem on $\mathbb{P}^1$, the genus-zero case of the global residue relation underlying Tate's treatment of Riemann–Roch and of duality for curves. It is used as the base case from which the residue theorem for a general function field over an algebraically closed field, [`AlgebraicCurve.residueTheoremK_of_isAlgClosed`](thm.html#AlgebraicCurve.residueTheoremK_of_isAlgClosed), is deduced.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.residueTheoremK_ratFunc_of_isAlgClosed
    (K : Type*) [Field K] [IsAlgClosed K] [DecidableEq (RatFunc K)]
    [AlgebraicCurve.HasCanonicalLocalResidueKStar K (RatFunc K)]
    [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := RatFunc K)]
    [∀ v : AlgebraicCurve.Place K (RatFunc K), v.DCoordGenerates] :
    AlgebraicCurve.ResidueTheoremK K (RatFunc K) := by sorry
