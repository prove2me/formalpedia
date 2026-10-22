-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_closed_preconnected_locally_convex_is_convex
-- name    : BirkhoffGlobalSection.closed_preconnected_locally_convex_is_convex
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-29T18:28:00.202482+00:00
-- url     : https://prove2.me/theorems/49a52bf8-4455-47ac-918c-7a406d201d8e
-- title:
--   Tietze--Nakajima local-to-global convexity in phase space
-- statement:
--   Let $K\subset\mathbb R^4$ be closed and connected. Suppose $K$ is locally convex in the following precise sense: for every $x\in K$, there is a neighborhood $U$ of $x$ such that $K\cap U$ is convex. Then
--
--   $$
--   K \text{ is convex}.
--   $$
--
--   This is the finite-dimensional Tietze--Nakajima local-to-global convexity theorem. It converts the local supporting geometry of a hypersurface and its enclosed region into global convexity.
--
--   **Formalization Note** Connectedness is expressed by `IsPreconnected`, and the ambient space is `Phase = Fin 4 → ℝ`.
-- source:
--   H. Tietze, Über Konvexheit im kleinen und im großen, Math. Z. 28 (1928), 697--707; S. Nakajima, Über konvexe Kurven und Flächen, Tôhoku Math. J. 29 (1928), 227--230. Finite-dimensional closed connected locally convex set theorem.

import Definitions.Def_BirkhoffGlobalSection
import Mathlib.Analysis.Convex.Basic

namespace BirkhoffGlobalSection

open scoped Topology

/-- Tietze--Nakajima local-to-global convexity in the finite-dimensional phase space:
a closed, connected set that is convex in a neighborhood of each of its points is convex. -/
theorem closed_preconnected_locally_convex_is_convex (K : Set Phase)
    (hclosed : IsClosed K)
    (hconn : IsPreconnected K)
    (hloc : ∀ x ∈ K, ∃ U : Set Phase, U ∈ 𝓝 x ∧ Convex ℝ (K ∩ U)) :
    Convex ℝ K := by sorry

end BirkhoffGlobalSection
