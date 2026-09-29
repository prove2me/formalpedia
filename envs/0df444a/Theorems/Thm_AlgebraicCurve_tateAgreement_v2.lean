-- Prove2me | Theorems.Thm_AlgebraicCurve_tateAgreement_v2
-- name    : AlgebraicCurve.tateAgreement_v2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/3dd2e2eb-3518-5a5c-86b9-4d886083278b
-- title:
--   Tate's residue equals the trace of the local residue
-- statement:
--   Let $K$ and $L$ be fields with $L$ a $K$-algebra, and assume [`AlgebraicCurve.IsCurveOver K L`](def/AlgebraicCurve_IsCurveOver.html#L15): every nonzero $f \in L$ admits a divisor $D$ on the places of $L$ over $K$ with $D(v) = \operatorname{ord}_v(f)$ at every place and $\deg D = 0$, each residue field $\kappa(v) = \mathcal{O}_v/\mathfrak{m}_v$ is a finite $K$-module, and $\Omega_{L/K}$ is free of rank $1$ over $L$; here a place is a valuation subring of $L$ containing the image of $K$, different from $L$, and a principal ideal ring. Assume further that $K$ is perfect and that every place $u$ of $L$ has $K$-finite residue field. Let `hfin` witness that for every place $u$ and all $f, g$ in the completion $\widehat{L}_u$ the range of the restricted commutator `tateCommRestrict (tateProj u) (lmulK u f) (lmulK u g)` — built from the $K$-linear projection of $\widehat{L}_u$ onto the $K$-submodule of integers along a chosen complement, and from multiplication by $f$ and by $g$ — is finite dimensional over $K$. The conclusion is `KwF4gRRTateAgreement K L hfin`: for every place $u$ with $K$-finite residue field and every $f \in \widehat{L}_u$, Tate's residue `tateRes u f (algebraMap L u.adicCompletion u.uniformizer)`, the commutator trace taken against the image of a chosen uniformizer of $u$, equals $\operatorname{Tr}_{\kappa(u)/K}$ of `kwHgfV352_localResidueCompletion u f`, the local residue `u.localResidue` evaluated at a chosen element of $L$ whose difference from $f$ lies in the completed integers at $u$.
--
--   This is the comparison theorem identifying Tate's trace-of-commutator definition of the residue on the completion $\widehat{L}_u$ with the trace to $K$ of the canonical local residue on the residue field at $u$, for the differential given by the chosen uniformizer. It is used in the residue-theory layer of the curve package, in particular by [`AlgebraicCurve.residueTraceCompletionCommute_v2`](thm.html#AlgebraicCurve.residueTraceCompletionCommute_v2).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_tateAgreement_v2.lean

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
import Definitions.Def_AlgebraicCurve_CanonicalLocalResidueInstanceV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.tateAgreement_v2
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [AlgebraicCurve.IsCurveOver K L] [PerfectField K]
    [∀ u : AlgebraicCurve.Place K L, u.FiniteResidue]
    (hfin : ModularCurve.KwF4gRRTate.KwF4gRRTateCommFinite K L) :
    ModularCurve.KwF4gRRTate.KwF4gRRTateAgreement K L hfin := by sorry
