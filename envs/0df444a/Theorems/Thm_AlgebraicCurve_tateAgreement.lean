-- Prove2me | Theorems.Thm_AlgebraicCurve_tateAgreement
-- name    : AlgebraicCurve.tateAgreement
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/e2d67bb2-5c38-50ea-b555-e4672b767b86
-- title:
--   Tate's residue agrees with the local residue trace
-- statement:
--   Let $K$ and $L$ be fields with $L$ a $K$-algebra such that [`AlgebraicCurve.IsCurveOver K L`](def/AlgebraicCurve_IsCurveOver.html#L15) holds: every nonzero $f \in L$ has an associated divisor whose value at each place is $\operatorname{ord}_v(f)$ and whose degree is $0$, every place $v$ of $L$ over $K$ (a valuation subring of $L$ containing the image of $K$, distinct from $L$ itself, and a principal ideal ring) has residue field finite over $K$, and $\Omega_{L/K}$ is free of rank $1$ over $L$. Assume in addition that $K$ is perfect and that each place $u$ carries the instance `FiniteResidue`, i.e. its residue field is a finite $K$-module. Let `hfin` witness `KwF4gRRTateCommFinite K L`: for every place $u$ and all $\hat f, \hat g$ in the adic completion $\widehat{L}_u$, the range of the endomorphism `tateCommRestrict` built from the projection `tateProj u` of $\widehat{L}_u$ onto the $K$-submodule of adic integers along a chosen complement and from the multiplication operators by $\hat f$ and $\hat g$ is finite-dimensional over $K$. The conclusion is `KwF4gRRTateAgreement K L hfin`: for every place $u$ with finite residue field and every $\hat f \in \widehat{L}_u$, the Tate residue `tateRes u` of $\hat f$ against the image in $\widehat{L}_u$ of a uniformizer of $u$ — the trace of the restricted commutator furnished by `hfin` — equals $\operatorname{Tr}_{\kappa(u)/K}$ of `kwHgfV352_localResidueCompletion u` $\hat f$, the local residue at $u$ evaluated on an element of $L$ differing from $\hat f$ by an adic integer.
--
--   This is the comparison, in Tate's treatment of residues of differentials on curves, between the commutator-trace definition of the residue on a completion and the trace to $K$ of the classical local residue, here at the pairing of an arbitrary element against a uniformizer. It is used by [`AlgebraicCurve.residueTraceCompletionCommute`](thm.html#AlgebraicCurve.residueTraceCompletionCommute) in establishing the compatibility of residues with traces on completions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_tateAgreement.lean

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
import Definitions.Def_AlgebraicCurve_CanonicalLocalResidueInstance

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.tateAgreement
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [AlgebraicCurve.IsCurveOver K L] [PerfectField K]
    [∀ u : AlgebraicCurve.Place K L, u.FiniteResidue]
    (hfin : ModularCurve.KwF4gRRTate.KwF4gRRTateCommFinite K L) :
    ModularCurve.KwF4gRRTate.KwF4gRRTateAgreement K L hfin := by sorry
