-- Prove2me | Theorems.Thm_AubinLipschitz_clarkeDeriv_invMap
-- name    : AubinLipschitz.clarkeDeriv_invMap
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:52:17.714453+00:00
-- url     : https://prove2.me/theorems/78a270bd-4df3-44b6-b220-df091eba472a
-- title:
--   §2, (18) — the Clarke derivative of the inverse is the inverse of the Clarke derivative
-- statement:
--   For a set-valued map $F$ between normed spaces and every $(x_0,y_0)\in\operatorname{graph}(F)$,
--
--   $$
--   CF(x_0,y_0)^{-1}=C(F^{-1})(y_0,x_0).
--   $$
--
--   This is what allows the goal to compute the derivative of the solution map from that of $F$.
--
--   Differences from the source:
--   - generalization: Banach spaces (§1, p.7) → normed spaces; reason: the Banach case is an instance, and completeness plays no role.
-- source:
--   Aubin, Lipschitz Behavior of Solutions to Convex Minimization Problems, IIASA WP-81-76 (1981), §2, display (18), p.17

import Mathlib
import Definitions.Def_AubinLipschitz_clarkeDeriv
import Definitions.Def_AubinLipschitz_invMap

namespace AubinLipschitz

/-- Aubin, Lipschitz Behavior of Solutions to Convex Minimization Problems, IIASA WP-81-76 (1981), §2, display (18), p.17: for every `(x₀, y₀) ∈ graph(F)`,
`CF(x₀, y₀)⁻¹ = C(F⁻¹)(y₀, x₀)`. -/
theorem clarkeDeriv_invMap {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (F : X → Set Y) (x₀ : X) (y₀ : Y) (h₀ : y₀ ∈ F x₀) :
    invMap (clarkeDeriv F x₀ y₀) = clarkeDeriv (invMap F) y₀ x₀ := by sorry

end AubinLipschitz
