-- Prove2me | Theorems.Thm_CompactOperators_compact_of_adjoint_comp_self_compact
-- name    : CompactOperators.compact_of_adjoint_comp_self_compact
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-01T22:20:11.650642+00:00
-- url     : https://prove2.me/theorems/ca6b238c-e729-4abc-9bda-eacf5bd80308
-- title:
--   Compactness from compact adjoint composition
-- statement:
--   Let $T:E\to F$ be a bounded linear operator between real or complex Hilbert spaces. If $T^*T$ is compact, then $T$ is compact. No separability or injectivity is assumed. This criterion applies, in particular, to proving that a positive square root of a compact positive operator is compact.
-- source:
--   Standard compact-operator criterion, proved by Cauchy–Schwarz and total boundedness. Related application: Kubrusly, Trace-Class and Nuclear Operators, arXiv:2204.06954v2, Proposition 5.3, https://arxiv.org/html/2204.06954v2#S5.

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Compact.Basic

universe u v w

namespace CompactOperators

theorem compact_of_adjoint_comp_self_compact {𝕜 : Type v} [RCLike 𝕜]
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    {F : Type w} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (T : E →L[𝕜] F) (hT : IsCompactOperator (T.adjoint ∘L T)) :
    IsCompactOperator T := by sorry

end CompactOperators
