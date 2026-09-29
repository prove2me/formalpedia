-- Prove2me | Theorems.Thm_BealeConvexMin_QuadSimplex_standard_form_minimal
-- name    : BealeConvexMin.QuadSimplex.standard_form_minimal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:34:41.480144+00:00
-- url     : https://prove2.me/theorems/ef9549db-a5a7-4ffc-b293-12df978d6915
-- title:
--   §3, p. 177 — in standard form $c_{00}$ cannot be decreased with the restricted nonbasic variables at zero
-- statement:
--   Consider a tableau whose objective $C=\sum_{k,l=0}^{N}c_{kl}z_kz_l$ ($z_0=1$) is convex: $(c_{kl})$ is symmetric and its quadratic block $(c_{kl})_{k,l=1}^{N}$ is positive semidefinite. Suppose $C$ is in **standard form**, i.e. contains no linear term in any free variable: $c_{k0}=0$ for every nonbasic free variable $z_k$. Then for every $z$ with $z_0=1$ and $z_k=0$ for every restricted nonbasic variable $z_k$,
--   $$C(z)\ \ge\ c_{00}.$$
--
--   In words: the value of $C$ in the associated solution cannot be decreased keeping the nonbasic restricted variables equal to zero. It follows that the value $c_{00}$ at a standard form depends only on which restricted variables are nonbasic, which is the potential in Beale's termination argument.
--
--   **Formalization Note** No sign constraint is placed on the other variables: the minimum is over the whole affine set on which the restricted nonbasic variables vanish, as in the paper.
-- source:
--   Beale, On Minimizing a Convex Function Subject to Linear Inequalities, J. R. Statist. Soc. B 17(2), 1955, https://doi.org/10.1111/j.2517-6161.1955.tb00191.x, p. 177 (PDF p. 5), §3, first two sentences of the paragraph after Lemma 2

import Mathlib
import Definitions.Def_BealeConvexMin_QuadSimplex_pivotC
import Definitions.Def_BealeConvexMin_QuadSimplex_Tableau

namespace BealeConvexMin.QuadSimplex

/-- Beale (1955), §3, p. 177: "When `C` is in standard form, its value in the associated solution,
`c_00`, cannot be decreased keeping the nonbasic restricted variables equal to zero." For a
symmetric `(c_kl)` with positive semidefinite quadratic block (convex `C`), in standard form, every
`z` with `z_0 = 1` and `z_k = 0` on the restricted nonbasic slots has `C(z) ≥ c_00`. -/
theorem standard_form_minimal {n N : ℕ} (T : Tableau n N) (hsymm : T.c.IsSymm)
    (hpsd : (T.c.submatrix Fin.succ Fin.succ).PosSemidef) (hstd : IsStandardForm T)
    (z : Fin (N + 1) → ℝ) (hz0 : z 0 = 1)
    (hzres : ∀ k : Fin N, T.lab k ≠ none → z k.succ = 0) :
    T.c 0 0 ≤ quadValue T.c z := by sorry

end BealeConvexMin.QuadSimplex
