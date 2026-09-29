-- Prove2me | Theorems.Thm_AlgebraicCurve_tateTraceCompat_of_isSeparable
-- name    : AlgebraicCurve.tateTraceCompat_of_isSeparable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/f5ada583-996c-5e80-8e5c-654a26d8f916
-- title:
--   Trace compatibility of Tate's local residue for separable F/E
-- statement:
--   Let $K$ be a field, $F$ a field extension of $K$, and $E$ an intermediate field, in the sense that $E$ is a $K$-algebra, $F$ is an $E$-algebra and the scalar actions form a tower $K \subseteq E \subseteq F$; assume $F$ is integral and separable over $E$. Assume furthermore that canonical local residue data are fixed at every place of $F$ and of $E$ over $K$ (the classes [`AlgebraicCurve.HasCanonicalLocalResidueKStar`](def/AlgebraicCurve_LocalResidue.html#L51) for $K \subseteq F$ and $K \subseteq E$, which assign to each place a residue functional killing $\pi^{-(n+1)}$ for all $n \ge 1$), and that every place of $F$ over $K$ and every place of $E$ over $K$ has residue field finite-dimensional over $K$; here a place of a field $L$ over $K$ is a valuation subring of $L$ containing the image of $K$, different from all of $L$, and a principal ideal ring. Let $h_F$ and $h_E$ be witnesses that Tate's commutators have finite rank: for every place $u$ of $F$ (respectively of $E$) and all $f, g$ in the adic completion $\widehat L_u$, the range of the restriction of the commutator built from the projector `tateProj` $u$ (projection onto the $K$-submodule of adic integers along a chosen complement) and the multiplication operators by $f$ and by $g$ is finite-dimensional over $K$, so that the residue symbol `tateRes` $u$ $f$ $g$, the trace of that restricted commutator, is defined. The conclusion is the proposition `KwF4gRRTateTraceCompat K F E h_F h_E`: for all instances making principal divisors available for $K \subseteq E$ and $K \subseteq F$ and making $F$ finite-dimensional over $E$, for every place $v$ of $E$, every place $w$ of $F$ in the fibre of $v$, and every $g \in F$, the residue symbol at $w$ of the image of $g$ in $\widehat F_w$ against the image of the uniformiser $\pi_v$ of $v$ equals the residue symbol at $v$ of the completed trace of $g$ from $w$ down to $v$ against the image of $\pi_v$ in $\widehat E_v$, the required finiteness instances being those provided by $h_F$ and $h_E$.
--
--   This is Tate's trace formula for the local residue symbol: the residue at a place $w$ of $F$ computed against a uniformiser pulled back from $E$ agrees with the residue at the place $v$ below of the local trace. It is used in the proofs that taking residues commutes with the trace map, [`AlgebraicCurve.residueTraceCompletionCommute`](thm.html#AlgebraicCurve.residueTraceCompletionCommute) and [`AlgebraicCurve.residueTraceCompletionCommute_v2`](thm.html#AlgebraicCurve.residueTraceCompletionCommute_v2); the finiteness witnesses appear explicitly as arguments because the proposition asserted depends on them.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_tateTraceCompat_of_isSeparable.lean

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
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_DedekindDomain_AdicValuation_InlineSpecific
import Definitions.Def_AlgebraicCurve_PlaceCompletion
import Definitions.Def_AlgebraicCurve_TateResidueCurrency

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.tateTraceCompat_of_isSeparable
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
    [Algebra.IsIntegral E F] [Algebra.IsSeparable E F]
    [AlgebraicCurve.HasCanonicalLocalResidueKStar K F] [AlgebraicCurve.HasCanonicalLocalResidueKStar K E]
    [∀ w : AlgebraicCurve.Place K F, w.FiniteResidue] [∀ v : AlgebraicCurve.Place K E, v.FiniteResidue]
    (hfinF : ModularCurve.KwF4gRRTate.KwF4gRRTateCommFinite K F)
    (hfinE : ModularCurve.KwF4gRRTate.KwF4gRRTateCommFinite K E) :
    ModularCurve.KwF4gRRTate.KwF4gRRTateTraceCompat K F E hfinF hfinE := by sorry
