-- Prove2me | Theorems.Thm_AlgebraicCurve_tateCommFinite
-- name    : AlgebraicCurve.tateCommFinite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/b8c365b4-ee08-5ae5-8611-88da8054c1dc
-- title:
--   Tate's commutator has finite K-rank at every place
-- statement:
--   Let $K$ and $L$ be fields with $L$ a $K$-algebra, and assume that every place $u$ of $L$ over $K$ — that is, every valuation subring of $L$ which contains the image of $K$, is not all of $L$, and is a principal ideal ring — has finite residue in the sense that the residue field of that valuation subring is a finite-dimensional $K$-module. The conclusion is the predicate [`ModularCurve.KwF4gRRTate.KwF4gRRTateCommFinite K L`](def/AlgebraicCurve_TateResidueCurrency.html#L300), which asserts: for every such place $u$ and all elements $fh$, $gh$ of the adic completion $\hat L_u$ of $L$ at the height-one prime associated with $u$, the range of `tateCommRestrict (tateProj u) (lmulK u fh) (lmulK u gh)` is finite-dimensional over $K$. Here `tateProj u` is the $K$-linear idempotent on $\hat L_u$ obtained by projecting onto the $K$-submodule `adicIntegersKSubmod u` along a chosen complement and then including it back, `lmulK u fh` and `lmulK u gh` are multiplication by $fh$ and by $gh$ on $\hat L_u$ as $K$-linear maps, and `tateCommRestrict` is Tate's commutator `tateComm` built from these three endomorphisms, restricted to the range of the projection, which it preserves.
--
--   This is the finite-potence (finite rank) input in Tate's construction of the abstract residue on a curve, where $\operatorname{res}_u(f\,dg)$ is the trace of the commutator $[p_u\mu_f, p_u\mu_g]$: without the finiteness of the range of that commutator the trace is not defined. It is used by [`AlgebraicCurve.residueTraceCompletionCommute`](thm.html#AlgebraicCurve.residueTraceCompletionCommute) and [`AlgebraicCurve.residueTraceCompletionCommute_v2`](thm.html#AlgebraicCurve.residueTraceCompletionCommute_v2), which compare the residue–trace construction with completion.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_tateCommFinite.lean

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

theorem AlgebraicCurve.tateCommFinite
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [∀ u : AlgebraicCurve.Place K L, u.FiniteResidue] :
    ModularCurve.KwF4gRRTate.KwF4gRRTateCommFinite K L := by sorry
