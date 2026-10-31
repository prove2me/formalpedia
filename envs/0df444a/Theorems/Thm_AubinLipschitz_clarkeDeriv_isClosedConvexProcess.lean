-- Prove2me | Theorems.Thm_AubinLipschitz_clarkeDeriv_isClosedConvexProcess
-- name    : AubinLipschitz.clarkeDeriv_isClosedConvexProcess
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:52:36.112289+00:00
-- url     : https://prove2.me/theorems/ddde4f77-c53d-4f79-b843-c6b7134c9914
-- title:
--   §2, p.16 — the Clarke derivative is a closed convex process
-- statement:
--   For a set-valued map $F$ between normed spaces and $(x_0,y_0)\in\operatorname{graph}(F)$, the Clarke derivative $CF(x_0,y_0)$ is a closed convex process: its graph, the Clarke tangent cone to $\operatorname{graph}(F)$ at $(x_0,y_0)$, is a closed convex cone.
--
--   This is the fact that lets the Robinson–Ursescu theorem apply to the Clarke derivative.
--
--   Differences from the source:
--   - generalization: Banach spaces (§1, p.7) → normed spaces; reason: the Banach case is an instance, and completeness plays no role.
-- source:
--   Aubin, Lipschitz Behavior of Solutions to Convex Minimization Problems, IIASA WP-81-76 (1981), §2, p.16; Introduction, p.5

import Mathlib
import Definitions.Def_AubinLipschitz_clarkeDeriv
import Definitions.Def_AubinLipschitz_IsClosedConvexProcess

namespace AubinLipschitz

/-- Aubin, Lipschitz Behavior of Solutions to Convex Minimization Problems, IIASA WP-81-76 (1981), §2, p.16 (and Introduction, p.5, "So, Clarke derivatives are closed convex
processes"): for `(x₀, y₀) ∈ graph(F)`, the Clarke derivative `CF(x₀, y₀)` is a closed convex
process. -/
theorem clarkeDeriv_isClosedConvexProcess {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (F : X → Set Y) (x₀ : X) (y₀ : Y) (h₀ : y₀ ∈ F x₀) :
    IsClosedConvexProcess (clarkeDeriv F x₀ y₀) := by sorry

end AubinLipschitz
