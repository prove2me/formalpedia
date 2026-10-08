-- Prove2me | Theorems.Thm_CompOT_Assignment_perm_feasible
-- name    : CompOT.Assignment.perm_feasible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:25:23.48481+00:00
-- url     : https://prove2.me/theorems/d3ee9abb-ae82-4a14-b6e6-daad8abc7887
-- title:
--   §2.3, p. 372 — every scaled permutation matrix is a uniform coupling
-- statement:
--   Let $n>0$ and let $u$ be the histogram with every entry equal to $1/n$. For every permutation $\sigma$ of $n$ indices, its scaled permutation matrix has both marginals equal to $u$:
--
--   $$P_\sigma\in U(u,u).$$
--
--   Thus each feasible assignment supplies a feasible point of the Kantorovich relaxation.
--
--   **Formalization Note** The printed text immediately after (2.12) gives the row and column sums as $\mathbf1_n$; the displayed definition of $P_\sigma$ makes them $\mathbf1_n/n$, as encoded here.
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), §2.3, p. 372, paragraph after (2.12)

import Mathlib
import Definitions.Def_CompOT_Assignment_Defs

namespace CompOT.Assignment

theorem perm_feasible {n : ℕ} (hn : 0 < n)
    (σ : Equiv.Perm (Fin n)) :
    permCoupling σ ∈ couplings (uniform n) (uniform n) := by sorry

end CompOT.Assignment
