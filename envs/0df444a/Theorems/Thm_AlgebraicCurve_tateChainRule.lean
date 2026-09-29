-- Prove2me | Theorems.Thm_AlgebraicCurve_tateChainRule
-- name    : AlgebraicCurve.tateChainRule
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/3923c003-06ed-5e6b-98e9-deccb859eeca
-- title:
--   Chain rule for Tate's residue along F/E
-- statement:
--   Let $K$, $E$, $F$ be fields with $K \subseteq E \subseteq F$ (compatible algebra structures, forming a scalar tower) such that $F$ is integral over $E$, assume that $F/K$ and $E/K$ each carry a chosen canonical local residue datum at every place (an instance of `HasCanonicalLocalResidueKStar`, where a place of $F$ over $K$ is a proper valuation subring of $F$ containing the image of $K$ whose valuation ring is a principal ideal ring), and assume every place $w$ of $F$ has finite residue, i.e. its residue field is a finite-dimensional $K$-module. Assume further the hypothesis `hfinF`, namely that for every place $u$ of $F$ and all $f,g$ in the adic completion $\widehat F_u$ the range of the restricted Tate commutator of the projection `tateProj u` onto the $K$-subspace of adic integers (along a chosen complement) with the multiplication operators by $f$ and $g$ is finite-dimensional over $K$, so that the trace `tateRes` is defined. The conclusion is the proposition `KwF4gRRTateChainRule K F E hfinF`: under the further assumptions, quantified inside that proposition, that $K$-principal divisors exist for $E$ and for $F$, that $F/E$ is finite-dimensional, that $\Omega_{E/K}$ and $\Omega_{F/K}$ are nontrivial, for every place $v$ of $E$ and every place $w$ of $F$ in the fibre of $v$, both satisfying `DCoordGenerates`, and every $f \in \widehat F_w$, one has $$\operatorname{tateRes}_w\bigl(f,\ \pi_v\bigr) = \operatorname{tateRes}_w\bigl(f \cdot \partial_w(\mathrm{d}\pi_v),\ \pi_w\bigr),$$ where $\pi_v$, $\pi_w$ denote the images in $\widehat F_w$ of the uniformisers of $v$ and $w$, and $\partial_w(\mathrm{d}\pi_v)$ is the `differentialCoeff` at $w$ of the pullback to $\Omega_{F/K}$ of the differential `v.dCoord` in $\Omega_{E/K}$.
--
--   This is the chain rule for Tate's trace-theoretic local residue along an extension $F/E$, corresponding to Tate's axiom (R4): changing the second argument from a uniformiser of the place below to a uniformiser of the place above is compensated by multiplying the first argument by the coordinate of the pulled-back differential. It is used in the comparison of residues with traces over completions, in [`AlgebraicCurve.residueTraceCompletionCommute`](thm.html#AlgebraicCurve.residueTraceCompletionCommute) and [`AlgebraicCurve.residueTraceCompletionCommute_v2`](thm.html#AlgebraicCurve.residueTraceCompletionCommute_v2).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_tateChainRule.lean

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

theorem AlgebraicCurve.tateChainRule
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
    [Algebra.IsIntegral E F]
    [AlgebraicCurve.HasCanonicalLocalResidueKStar K F] [AlgebraicCurve.HasCanonicalLocalResidueKStar K E]
    [∀ w : AlgebraicCurve.Place K F, w.FiniteResidue]
    (hfinF : ModularCurve.KwF4gRRTate.KwF4gRRTateCommFinite K F) :
    ModularCurve.KwF4gRRTate.KwF4gRRTateChainRule K F E hfinF := by sorry
