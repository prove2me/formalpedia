-- Prove2me | Theorems.Thm_BealeConvexMin_QuadSimplex_no_return_standard_form
-- name    : BealeConvexMin.QuadSimplex.no_return_standard_form
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T11:36:04.341284+00:00
-- url     : https://prove2.me/theorems/e13bc6ad-fe34-45bc-b4e3-1d995d07f3c3
-- title:
--   §3, p. 177 — no return to a standard form with the same restricted nonbasic set
-- statement:
--   Let $T_0\to T_1\to\cdots\to T_j$ be a finite run of Beale's iteration. Assume the initial objective is convex ($(c_{kl})$ symmetric with positive semidefinite quadratic block), the initial labels are consistent, and at every tableau $T_0,\dots,T_j$ every basic restricted variable is strictly positive in the associated solution. If $i<j$ and both $T_i$ and $T_j$ are in standard form, then
--   $$\{\text{restricted nonbasic variables of }T_i\}\neq\{\text{restricted nonbasic variables of }T_j\}.$$
--
--   In Beale's words, the iteration "can never return to a standard form with the same set of restricted nonbasic variables, even with a different set of free nonbasic variables". Since there are finitely many sets of restricted variables, the iteration passes through finitely many standard forms.
--
--   **Formalization Note** The statement is about a finite run, so it is not implied by the termination theorem. Positivity of the basic variables replaces Charnes's $\varepsilon$-perturbations.
-- source:
--   Beale, On Minimizing a Convex Function Subject to Linear Inequalities, J. R. Statist. Soc. B 17(2), 1955, https://doi.org/10.1111/j.2517-6161.1955.tb00191.x, p. 177 (PDF p. 5), §3, third sentence of the paragraph after Lemma 2

import Mathlib
import Definitions.Def_BealeConvexMin_QuadSimplex_pivotC
import Definitions.Def_BealeConvexMin_QuadSimplex_Tableau
import Definitions.Def_BealeConvexMin_QuadSimplex_BealeStep

namespace BealeConvexMin.QuadSimplex

/-- Beale (1955), §3, p. 177: "it can never return to a standard form with the same set of
restricted nonbasic variables, even with a different set of free nonbasic variables". Along a
finite run `T 0 → T 1 → ⋯ → T j` of the iteration, started from a symmetric `(c_kl)` with positive
semidefinite quadratic block and consistent labels, with every basic restricted variable strictly
positive at every tableau, two standard-form tableaux `T i`, `T j` with `i < j` have different
sets of restricted nonbasic variables. -/
theorem no_return_standard_form {n N : ℕ} (T : ℕ → Tableau n N) (hsymm : (T 0).c.IsSymm)
    (hpsd : ((T 0).c.submatrix Fin.succ Fin.succ).PosSemidef) (hlab : LabelsConsistent (T 0))
    {i j : ℕ} (hij : i < j) (hstep : ∀ k < j, BealeStep (T k) (T (k + 1)))
    (hpos : ∀ k ≤ j, BasicPositive (T k))
    (hi : IsStandardForm (T i)) (hj : IsStandardForm (T j)) :
    restrictedNonbasic (T i) ≠ restrictedNonbasic (T j) := by sorry

end BealeConvexMin.QuadSimplex
