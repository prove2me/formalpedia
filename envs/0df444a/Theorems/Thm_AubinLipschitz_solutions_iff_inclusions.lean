-- Prove2me | Theorems.Thm_AubinLipschitz_solutions_iff_inclusions
-- name    : AubinLipschitz.solutions_iff_inclusions
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:51:40.479+00:00
-- url     : https://prove2.me/theorems/6282a486-e063-4858-a9f6-84e0a6aba4c0
-- title:
--   §5, (3) ⇔ (4) — solutions of the optimization problem are the solutions of the inclusions
-- statement:
--   Let $X,Y$ be finite-dimensional, $A_0:X\to Y$ linear, and $U:X\to\mathbb R\cup\{+\infty\}$, $V:Y\to\mathbb R\cup\{+\infty\}$ proper, lower semicontinuous and convex. For $p_0\in X^*$, $y_0\in Y$, a pair $(x_0,q_0)\in X\times Y^*$ solves the optimization problem (3) if and only if
--
--   $$
--   p_0\in\partial U(x_0)+A_0^*q_0,\qquad y_0\in -A_0x_0+\partial V^*(q_0).
--   $$
--
--   This turns the optimization problem into a system of inclusions, which is what the set-valued Inverse Function Theorem can act on.
--
--   Differences from the source:
--   - generalization: the paper's §5 has assumption (2) in force → Lean does not assume (2); reason: the equivalence is a Fenchel-duality fact that does not use (2), and adding (2) gives the paper's statement.
-- source:
--   Aubin, Lipschitz Behavior of Solutions to Convex Minimization Problems, IIASA WP-81-76 (1981), §5, (3)–(4), p.31

import Mathlib
import Definitions.Def_RockafellarMaxMono_Shared_ProperConvex
import Definitions.Def_RockafellarMaxMono_Shared_Subdiff
import Definitions.Def_AubinLipschitz_IsPrimalDualSolution
import Definitions.Def_AubinLipschitz_paramMap
import Definitions.Def_AubinLipschitz_subdiffConj
open RockafellarMaxMono.Shared

namespace AubinLipschitz

/-- Aubin, Lipschitz Behavior of Solutions to Convex Minimization Problems, IIASA WP-81-76 (1981), §5, (3) ⇔ (4), p.31: the solutions `(x₀, q₀)` of the optimization problem (3) are the
solutions of the system of inclusions (4), `p₀ ∈ ∂U(x₀) + A₀*q₀`, `y₀ ∈ −A₀x₀ + ∂V*(q₀)`. -/
theorem solutions_iff_inclusions {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    (U : X → EReal) (V : Y → EReal) (hU : ProperConvex U) (hUlsc : LowerSemicontinuous U)
    (hV : ProperConvex V) (hVlsc : LowerSemicontinuous V) (A₀ : X →L[ℝ] Y)
    (p₀ : StrongDual ℝ X) (y₀ : Y) (x₀ : X) (q₀ : StrongDual ℝ Y) :
    IsPrimalDualSolution U V A₀ p₀ y₀ x₀ q₀ ↔
      (p₀, y₀, A₀) ∈ paramMap (subdiff U) (subdiffConj V) (x₀, q₀) := by sorry

end AubinLipschitz
