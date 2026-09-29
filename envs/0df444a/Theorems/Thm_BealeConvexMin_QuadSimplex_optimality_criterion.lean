-- Prove2me | Theorems.Thm_BealeConvexMin_QuadSimplex_optimality_criterion
-- name    : BealeConvexMin.QuadSimplex.optimality_criterion
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:34:12.619709+00:00
-- url     : https://prove2.me/theorems/a5e29c01-deef-4ed1-bf12-8d4164d29550
-- title:
--   §3, p. 175 — no profitable nonbasic variable implies an absolute minimum
-- statement:
--   Consider a tableau whose objective $C=\sum_{k,l=0}^{N}c_{kl}z_kz_l$ ($z_0=1$) is convex: $(c_{kl})$ is symmetric and its quadratic block $(c_{kl})_{k,l=1}^{N}$ is positive semidefinite. Suppose no nonbasic variable can profitably be altered, i.e.
--   1. $c_{k0}=0$ for every nonbasic free variable $z_k$, and
--   2. $c_{k0}\ge0$ for every nonbasic restricted variable $z_k$.
--
--   Then the associated solution is an absolute minimum of $C$ over the feasible region: for every $z$ with $z_0=1$, $z_k\ge0$ for every restricted nonbasic $z_k$, and $x_h=\sum_{l}a_{hl}z_l\ge0$ for every restricted variable $x_h$,
--   $$C(z)=\sum_{k,l=0}^{N}c_{kl}z_kz_l\ \ge\ c_{00}.$$
--
--   This is the optimality criterion at which the iteration stops: a tableau from which no nonbasic variable can profitably be altered solves the problem.
--
--   **Formalization Note** Convexity of $C$ is stated in tableau coordinates as positive semidefiniteness of the quadratic block. The feasible region is written in the current nonbasic coordinates: all restricted variables nonnegative.
-- source:
--   Beale, On Minimizing a Convex Function Subject to Linear Inequalities, J. R. Statist. Soc. B 17(2), 1955, https://doi.org/10.1111/j.2517-6161.1955.tb00191.x, p. 175 (PDF p. 3), §3, paragraph after (3.1)

import Mathlib
import Definitions.Def_BealeConvexMin_QuadSimplex_pivotC
import Definitions.Def_BealeConvexMin_QuadSimplex_Tableau
import Definitions.Def_BealeConvexMin_QuadSimplex_BealeStep

namespace BealeConvexMin.QuadSimplex

/-- Beale (1955), §3, p. 175, paragraph after (3.1): if no nonbasic variable can profitably be
altered (no free slot with `c_k0 ≠ 0`, no restricted slot with `c_k0 < 0`) and `C` is convex
(symmetric `(c_kl)` whose quadratic block `(c_kl)_{k,l ≥ 1}` is positive semidefinite), then the
associated solution is an absolute minimum: every feasible point `z` (with `z_0 = 1`, every
restricted nonbasic variable `≥ 0` and every restricted variable `x_j = Σ_l row j l · z_l ≥ 0`)
has `C(z) ≥ c_00`. -/
theorem optimality_criterion {n N : ℕ} (T : Tableau n N) (hsymm : T.c.IsSymm)
    (hpsd : (T.c.submatrix Fin.succ Fin.succ).PosSemidef)
    (hopt : ∀ k : Fin N, ¬ IsProfitable T k)
    (z : Fin (N + 1) → ℝ) (hz0 : z 0 = 1)
    (hzres : ∀ k : Fin N, T.lab k ≠ none → 0 ≤ z k.succ)
    (hrow : ∀ j : Fin n, 0 ≤ ∑ l, T.row j l * z l) :
    T.c 0 0 ≤ quadValue T.c z := by sorry

end BealeConvexMin.QuadSimplex
