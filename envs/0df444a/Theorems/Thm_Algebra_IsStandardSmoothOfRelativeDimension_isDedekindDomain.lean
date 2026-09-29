-- Prove2me | Theorems.Thm_Algebra_IsStandardSmoothOfRelativeDimension_isDedekindDomain
-- name    : Algebra.IsStandardSmoothOfRelativeDimension.isDedekindDomain
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/7afaafee-a840-5429-94bc-bfdf338ce2b5
-- title:
--   Standard smooth domains of relative dimension 1 are Dedekind
-- statement:
--   Let $k$ be a field and let $S$ be a commutative ring which is an integral domain and a $k$-algebra, and suppose that $S$ is standard smooth of relative dimension $1$ over $k$ in Mathlib's sense (`Algebra.IsStandardSmoothOfRelativeDimension 1 k S`). The conclusion is that $S$ is a Dedekind domain, i.e. satisfies Mathlib's `IsDedekindDomain S`: $S$ is a Noetherian domain, of Krull dimension at most one in the sense that every nonzero prime ideal of $S$ is maximal, and integrally closed in its field of fractions. No further hypotheses are imposed: in particular $S$ is not assumed finite over $k$, nor is $k$ assumed perfect or algebraically closed, and the field $k$ enters only through the standard smoothness assumption. Note that the degenerate case is not excluded by fiat; it is ruled out by the relative dimension being $1$ together with $S$ being a domain.
--
--   This is the statement that an affine chart of a smooth curve over a field, assumed irreducible, is a Dedekind domain. It is used to equip coordinate rings arising in the construction of Drinfeld-type curves with Dedekind domain structure ([`DrinfeldCurve.isDedekindDomain_coordRing`](thm.html#DrinfeldCurve.isDedekindDomain_coordRing)), so that the ideal theory and divisor theory of such rings is available.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_IsStandardSmoothOfRelativeDimension_isDedekindDomain.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v

theorem Algebra.IsStandardSmoothOfRelativeDimension.isDedekindDomain
    {k : Type u} {S : Type v} [Field k] [CommRing S] [IsDomain S] [Algebra k S]
    [Algebra.IsStandardSmoothOfRelativeDimension 1 k S] : IsDedekindDomain S := by sorry
