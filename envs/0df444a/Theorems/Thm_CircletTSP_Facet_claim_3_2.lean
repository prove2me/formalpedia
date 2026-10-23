-- Prove2me | Theorems.Thm_CircletTSP_Facet_claim_3_2
-- name    : CircletTSP.Facet.claim_3_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:18:07.90447+00:00
-- url     : https://prove2.me/theorems/cdc10e78-4b36-41ff-a493-6546bd38a882
-- title:
--   Claim 3.2, p. 8 — Inequality (2) is valid for n = 4
-- statement:
--   For $n=4$ we have $d=2$, $c_1=1$ and $c_2=0$, so Inequality (2) reads $t_1+0\,t_2\ge 2$. The claim is that every Hamiltonian cycle $H$ on four cities satisfies it:
--   $$\sum_{i=1}^{2} c_i\, t_i(\chi_H)\ \ge\ 4-2 .$$
--
--   This is the base case of the minimal-counterexample argument for Theorem 3.1.
--
--   **Formalization Note** Hamiltonian cycles are orderings `π : Equiv.Perm (Fin 4)` with incidence vector `MetricTSP.tourVec π`.
-- source:
--   Gutekunst, Williamson, The Circlet Inequalities, arXiv:2012.12363v1, p. 8, Claim 3.2

import Mathlib
import Definitions.Def_MetricTSP_tour_vector
import Definitions.Def_CircletTSP_Facet_Setting

namespace CircletTSP.Facet

/-- Claim 3.2 (p. 8): Inequality (2) is valid for `n = 4`, i.e. every Hamiltonian cycle on
four cities satisfies `t₁ + 0·t₂ ≥ 2`. -/
theorem claim_3_2 (π : Equiv.Perm (Fin 4)) :
    (4 : ℝ) - 2 ≤ circletForm 4 (MetricTSP.tourVec π) := by sorry

end CircletTSP.Facet
