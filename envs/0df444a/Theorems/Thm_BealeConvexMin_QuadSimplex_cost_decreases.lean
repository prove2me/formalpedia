-- Prove2me | Theorems.Thm_BealeConvexMin_QuadSimplex_cost_decreases
-- name    : BealeConvexMin.QuadSimplex.cost_decreases
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:35:32.048693+00:00
-- url     : https://prove2.me/theorems/7b664aa4-f36b-46e4-8e86-fe7114613dca
-- title:
--   §3, p. 177 — $C$ decreases at every step
-- statement:
--   Let $T$ be a tableau with symmetric $(c_{kl})$ and consistent labels, in which every basic restricted variable is strictly positive in the associated solution ($a_{h0}>0$ for every basic $x_h$). If one step of Beale's iteration leads from $T$ to $T'$, then the value of $C$ in the associated solution strictly decreases:
--   $$c'_{00}<c_{00}.$$
--
--   The strict decrease is what prevents the iteration from revisiting a standard form with the same set of restricted nonbasic variables.
--
--   **Formalization Note** The strict positivity of the basic variables is the effect of Charnes's $\varepsilon$-perturbations (p. 174, "We ensure that the $a_{h0}$ are always positive, and not zero"); it makes the step length positive. Convexity of $C$ is not needed for this single-step statement.
-- source:
--   Beale, On Minimizing a Convex Function Subject to Linear Inequalities, J. R. Statist. Soc. B 17(2), 1955, https://doi.org/10.1111/j.2517-6161.1955.tb00191.x, p. 177 (PDF p. 5), §3, third sentence of the paragraph after Lemma 2 ('since C decreases at every step'); p. 174 (PDF p. 2), eq. (2.4)

import Mathlib
import Definitions.Def_BealeConvexMin_QuadSimplex_pivotC
import Definitions.Def_BealeConvexMin_QuadSimplex_Tableau
import Definitions.Def_BealeConvexMin_QuadSimplex_BealeStep

namespace BealeConvexMin.QuadSimplex

/-- Beale (1955), §3, p. 177: "`C` decreases at every step". If `(c_kl)` is symmetric, the labels
are consistent and every basic restricted variable is strictly positive in the associated
solution (the ε-perturbation device, p. 174), then one step of the iteration strictly decreases
the value `c_00` of `C` in the associated solution. -/
theorem cost_decreases {n N : ℕ} (T T' : Tableau n N) (hsymm : T.c.IsSymm)
    (hlab : LabelsConsistent T) (hpos : BasicPositive T) (hstep : BealeStep T T') :
    T'.c 0 0 < T.c 0 0 := by sorry

end BealeConvexMin.QuadSimplex
