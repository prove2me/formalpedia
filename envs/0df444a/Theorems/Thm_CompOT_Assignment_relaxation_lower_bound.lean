-- Prove2me | Theorems.Thm_CompOT_Assignment_relaxation_lower_bound
-- name    : CompOT.Assignment.relaxation_lower_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-08T00:25:18.329676+00:00
-- url     : https://prove2.me/theorems/3e3bdad1-cc9d-4f80-a22a-822a4714506d
-- title:
--   §2.3, p. 372 — the Kantorovich minimum is no larger than the assignment minimum
-- statement:
--   Let $n>0$, let $u$ be the uniform histogram on $n$ points, and let $C$ be any real $n\times n$ cost matrix. Minimizing over every coupling can only decrease the minimum relative to restricting to scaled permutation matrices:
--
--   $$L_C(u,u)\le\min_{\sigma\in\operatorname{Perm}(n)}\langle C,P_\sigma\rangle=\min_{\sigma\in\operatorname{Perm}(n)} A_C(\sigma).$$
--
--   This is the lower bound supplied by the linear relaxation before Proposition 2.1 proves that the bound is attained by an assignment.
--
--   **Formalization Note** Both minima are encoded as real infima. At $n>0$, the finite permutation set is nonempty and the coupling polytope is nonempty and bounded, so these infima agree with the book's minima.
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), §2.3, p. 372, final display before Proposition 2.1

import Mathlib
import Definitions.Def_CompOT_Assignment_Defs

namespace CompOT.Assignment

theorem relaxation_lower_bound {n : ℕ} (hn : 0 < n)
    (C : Matrix (Fin n) (Fin n) ℝ) :
    otCost C (uniform n) (uniform n) ≤ assignmentMin C := by sorry

end CompOT.Assignment
