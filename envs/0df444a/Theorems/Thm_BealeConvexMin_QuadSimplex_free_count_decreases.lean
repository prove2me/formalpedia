-- Prove2me | Theorems.Thm_BealeConvexMin_QuadSimplex_free_count_decreases
-- name    : BealeConvexMin.QuadSimplex.free_count_decreases
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:36:30.42422+00:00
-- url     : https://prove2.me/theorems/492dc0af-05c9-44f3-9895-3d4ffb8ebab8
-- title:
--   §3, p. 177 — $s$ cannot increase and decreases within $s_0$ steps unless standard form is reached
-- statement:
--   Let $T_0$ have a symmetric matrix $(c_{kl})$, let $C$ not be in standard form at $T_0$, and let $s_0$ be the number of nonbasic free variables of $T_0$. Let $T_0\to T_1\to\cdots\to T_{s_0}$ be $s_0$ steps of Beale's iteration. Then there is $i\le s_0$ such that
--
--   1. $T_i$ is in standard form, or $T_i$ has fewer than $s_0$ nonbasic free variables; and
--   2. none of $T_0,\dots,T_i$ has more than $s_0$ nonbasic free variables.
--
--   This is Beale's "if $C$ is not in standard form and $s=s_0$ say, then $s$ cannot increase, and must decrease after at most $s_0$ steps, unless $C$ meanwhile achieves standard form". Together with the no-return statement it yields the termination of the iteration.
--
--   **Formalization Note** $s_0$ steps are assumed to exist; the conclusion locates the first tableau at which standard form is reached or $s$ drops. The rule that a free variable is chosen whenever one is profitable is part of the step.
-- source:
--   Beale, On Minimizing a Convex Function Subject to Linear Inequalities, J. R. Statist. Soc. B 17(2), 1955, https://doi.org/10.1111/j.2517-6161.1955.tb00191.x, p. 177 (PDF p. 5), §3, second paragraph after Lemma 2, second-last sentence

import Mathlib
import Definitions.Def_BealeConvexMin_QuadSimplex_pivotC
import Definitions.Def_BealeConvexMin_QuadSimplex_Tableau
import Definitions.Def_BealeConvexMin_QuadSimplex_BealeStep

namespace BealeConvexMin.QuadSimplex

/-- Beale (1955), §3, p. 177: "if `C` is not in standard form and `s = s_0` say, then `s` cannot
increase, and must decrease after at most `s_0` steps, unless `C` meanwhile achieves standard
form". Let `T 0` have a symmetric `(c_kl)`, not be in standard form, and have `s_0 = numFree (T 0)`
nonbasic free variables, and let `T 0 → T 1 → ⋯ → T s_0` be steps of the iteration. Then some
`i ≤ s_0` has `T i` in standard form or `s(T i) < s_0`, and `s(T i') ≤ s_0` for all `i' ≤ i`. -/
theorem free_count_decreases {n N : ℕ} (T : ℕ → Tableau n N) (hsymm : (T 0).c.IsSymm)
    (hns : ¬ IsStandardForm (T 0))
    (hstep : ∀ k < numFree (T 0), BealeStep (T k) (T (k + 1))) :
    ∃ i ≤ numFree (T 0), (IsStandardForm (T i) ∨ numFree (T i) < numFree (T 0)) ∧
      ∀ i' ≤ i, numFree (T i') ≤ numFree (T 0) := by sorry

end BealeConvexMin.QuadSimplex
