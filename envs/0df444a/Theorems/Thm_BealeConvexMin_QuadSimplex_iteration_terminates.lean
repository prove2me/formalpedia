-- Prove2me | Theorems.Thm_BealeConvexMin_QuadSimplex_iteration_terminates
-- name    : BealeConvexMin.QuadSimplex.iteration_terminates
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:36:52.172459+00:00
-- url     : https://prove2.me/theorems/1415b1ee-0c60-46e5-aee6-2f9f5eb40935
-- title:
--   §3, p. 177 — Beale's simplex method for a convex quadratic function terminates
-- statement:
--   Consider Beale's extension of the simplex method to minimizing a convex quadratic function $C$ of nonnegative variables subject to linear equations. The current state is a tableau: each restricted variable $x_h$ is written as $x_h=a_{h0}+\sum_{l=1}^{N}a_{hl}z_l$ in the nonbasic variables $z_1,\dots,z_N$, which are restricted or free, and $C=\sum_{k,l=0}^{N}c_{kl}z_kz_l$ with $z_0=1$.
--
--   Let the initial tableau have
--   1. a symmetric matrix $(c_{kl})$ whose quadratic block $(c_{kl})_{k,l=1}^{N}$ is positive semidefinite (convexity of $C$), and
--   2. consistent labels (each restricted nonbasic variable in exactly one slot, with the unit row).
--
--   Then there is no infinite sequence of tableaux $T_0,T_1,T_2,\dots$ starting at the given one such that each $T_{k+1}$ arises from $T_k$ by one step of the iteration and every basic restricted variable is strictly positive in the associated solution of every $T_k$:
--   $$\neg\,\exists\,(T_k)_{k\ge0}:\ T_0=T,\quad T_k\to T_{k+1}\ \text{for all }k,\quad a^{(k)}_{h0}>0\ \text{for all }k\text{ and all basic }x_h .$$
--
--   In the paper's words, "the iteration must terminate". Every run therefore reaches a tableau from which no step is possible; what such a tableau looks like (an absolute minimum, by the optimality criterion of p. 175, or a ray along which $C$ decreases indefinitely) is not part of this statement.
--
--   **Formalization Note** The paper keeps every $a_{h0}$ of a basic variable positive with Charnes's $\varepsilon$-perturbations; here this is a hypothesis on the run rather than a perturbation scheme. The problem data $A,B$ enter only through the initial tableau, and phase 1 is out of scope. No bound on the number of steps is claimed, as in the paper.
-- source:
--   Beale, On Minimizing a Convex Function Subject to Linear Inequalities, J. R. Statist. Soc. B 17(2), 1955, https://doi.org/10.1111/j.2517-6161.1955.tb00191.x, p. 177 (PDF p. 5), §3, paragraphs after Lemma 2 (announced on p. 175)

import Mathlib
import Definitions.Def_BealeConvexMin_QuadSimplex_pivotC
import Definitions.Def_BealeConvexMin_QuadSimplex_Tableau
import Definitions.Def_BealeConvexMin_QuadSimplex_BealeStep

namespace BealeConvexMin.QuadSimplex

/-- Beale (1955), §3, p. 177: the iteration for a convex quadratic `C` terminates. From an initial
tableau with symmetric `(c_kl)`, positive semidefinite quadratic block (convex `C`) and consistent
labels, there is no infinite run `T 0 → T 1 → ⋯` of steps along which every basic restricted
variable stays strictly positive in the associated solution (the ε-perturbation device of p. 174,
stated as a hypothesis on the run). -/
theorem iteration_terminates {n N : ℕ} (T₀ : Tableau n N) (hsymm : T₀.c.IsSymm)
    (hpsd : (T₀.c.submatrix Fin.succ Fin.succ).PosSemidef) (hlab : LabelsConsistent T₀) :
    ¬ ∃ T : ℕ → Tableau n N, T 0 = T₀ ∧ (∀ k, BealeStep (T k) (T (k + 1))) ∧
      ∀ k, BasicPositive (T k) := by sorry

end BealeConvexMin.QuadSimplex
