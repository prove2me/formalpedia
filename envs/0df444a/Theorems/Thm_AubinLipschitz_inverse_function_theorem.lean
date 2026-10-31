-- Prove2me | Theorems.Thm_AubinLipschitz_inverse_function_theorem
-- name    : AubinLipschitz.inverse_function_theorem
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:52:25.644858+00:00
-- url     : https://prove2.me/theorems/38324337-55c6-41a0-9af1-ebe16c3ffe39
-- title:
--   §3, Theorem 1 — the Inverse Function Theorem for set-valued maps
-- statement:
--   Let $F$ be a closed set-valued map from $X$ to $Y$ with $X$, $Y$ finite dimensional, and $(x_0,y_0)\in\operatorname{graph}(F)$. If the Clarke derivative $CF(x_0,y_0)$ is surjective, then $F^{-1}$ is pseudo-Lipschitz around $(y_0,x_0)$.
--
--   For a continuously differentiable single-valued map this recovers the local solvability part of the usual inverse function theorem.
--
--   Differences from the source: none.
-- source:
--   Aubin, Lipschitz Behavior of Solutions to Convex Minimization Problems, IIASA WP-81-76 (1981), §3, Theorem 1, p.22

import Mathlib
import Definitions.Def_AubinLipschitz_clarkeDeriv
import Definitions.Def_AubinLipschitz_graphOf
import Definitions.Def_AubinLipschitz_invMap
import Definitions.Def_AubinLipschitz_IsSurjectiveProcess
import Definitions.Def_AubinLipschitz_PseudoLipschitzAround

namespace AubinLipschitz

/-- Aubin, Lipschitz Behavior of Solutions to Convex Minimization Problems, IIASA WP-81-76 (1981), §3, Theorem 1 (the Inverse Function Theorem), p.22: let `F` be a closed set-valued map
between finite-dimensional spaces and `(x₀, y₀) ∈ graph(F)`. If the Clarke derivative
`CF(x₀, y₀)` is surjective, then `F⁻¹` is pseudo-Lipschitz around `(y₀, x₀)`. -/
theorem inverse_function_theorem {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    (F : X → Set Y) (hF : IsClosed (graphOf F)) (x₀ : X) (y₀ : Y) (h₀ : y₀ ∈ F x₀)
    (hsurj : IsSurjectiveProcess (clarkeDeriv F x₀ y₀)) :
    PseudoLipschitzAround (invMap F) y₀ x₀ := by sorry

end AubinLipschitz
