-- Prove2me | Theorems.Thm_ConstrSOSP_searchReduces_trans
-- name    : ConstrSOSP.searchReduces_trans
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:58:49.473508+00:00
-- url     : https://prove2.me/theorems/721f5800-6f99-4ba7-bde9-3faf522cdb17
-- title:
--   Polynomial-time search reductions compose
-- statement:
--   **Theorem.** If a search problem $Q$ reduces in polynomial time to $R$, and $R$ reduces in polynomial time to $S$, then $Q$ reduces in polynomial time to $S$.
--
--   This is what lets PLS-hardness be shown by a chain of reductions: LocalOpt to Iter (Morioka), then Iter to the stationarity problems (the paper's construction).
--
--   **Formalization Note** Reductions are pairs of polynomial-time maps on Cook Turing machines, the answer map being correct for every answer.
--
--   Differences from the source:
--   - encoding: search problems and polynomial-time reductions, not defined in the paper → finite-string search problems (public SearchProblem) and Levin reductions on Cook Turing machines correct for every answer (public SearchReduces); circuits as binary codes, [2ⁿ] as n-bit strings read as 1 + binary value; reason: the standard meaning of reductions between TFNP problems; same instances
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), §4.1, p.17 (PLS defined by reduction to LocalOpt; implicit in every "PLS-hard")

import Mathlib
import Definitions.Def_TetrisHard_Rows_Search
import Definitions.Def_CardinalMatching_SearchReduces

namespace ConstrSOSP

open CardinalMatching

/-- **Polynomial-time search reductions compose** (arXiv:2604.02285, 2 Nov 2026, §4.1, p.17: "PLS
is traditionally defined as the complexity class which contains all TFNP problems that reduce to
the PLS-complete Localopt problem"; PLS-hardness of a problem is then shown by a chain of
reductions from LocalOpt).

If `Q` reduces to `R` and `R` reduces to `S` (each by a pair of polynomial-time instance and
answer maps on Cook's Turing machines, correct for every answer), then `Q` reduces to `S`. -/
theorem searchReduces_trans (Q R S : TetrisHard.Rows.SearchProblem) (hQR : SearchReduces Q R)
    (hRS : SearchReduces R S) : SearchReduces Q S := by sorry

end ConstrSOSP
