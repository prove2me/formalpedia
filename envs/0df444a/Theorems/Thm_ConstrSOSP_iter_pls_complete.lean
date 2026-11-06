-- Prove2me | Theorems.Thm_ConstrSOSP_iter_pls_complete
-- name    : ConstrSOSP.iter_pls_complete
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T21:03:54.330638+00:00
-- url     : https://prove2.me/theorems/b3dcfad3-4e42-47f3-b69c-320eac89dd76
-- title:
--   Iter is PLS-complete: LocalOpt and Iter reduce to each other
-- statement:
--   Let LocalOpt be the problem of Definition 4.1 (given circuits $p,g:[2^n]\to[2^n]$, find $v$ with $p(g(v))\ge p(v)$) and Iter the problem of Definition 4.2 (given $C:[2^n]\to[2^n]$ with $C(1)>1$, find $v$ with $C(v)<v$, or $C(v)>v$ and $C(C(v))=C(v)$).
--
--   **Theorem.** LocalOpt reduces to Iter, and Iter reduces to LocalOpt, by polynomial-time search reductions.
--
--   Since the paper defines PLS as the TFNP problems reducing to LocalOpt, the first reduction says Iter is PLS-hard and the second that it lies in PLS. The paper uses the first as the starting point of its hardness proof.
--
--   **Formalization Note** A search reduction consists of a polynomial-time instance map and a polynomial-time answer map (Cook Turing machines); the answer map must be correct for every answer of the target problem.
--
--   Differences from the source:
--   - encoding: search problems and polynomial-time reductions, not defined in the paper → finite-string search problems (public SearchProblem) and Levin reductions on Cook Turing machines correct for every answer (public SearchReduces); circuits as binary codes, [2ⁿ] as n-bit strings read as 1 + binary value; reason: the standard meaning of reductions between TFNP problems; same instances
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), §4.1, p.17 ("the PLS-complete problem Iter", used without proof; classical, Morioka 2001)

import Mathlib
import Definitions.Def_CardinalMatching_SearchReduces
import Definitions.Def_ConstrSOSP_LocalOpt
import Definitions.Def_ConstrSOSP_Iter

namespace ConstrSOSP

open CardinalMatching

/-- **Iter is PLS-complete** (Kontogiannis, Panageas & Pollatos, arXiv:2604.02285, version of
2 November 2026, §4.1, p.17: "To prove our hardness result, we will make use of the PLS-complete
problem Iter (see also Figure 4.1), which is formally defined as follows."; used without proof;
classical, Morioka 2001).

LocalOpt and Iter reduce to each other by polynomial-time search reductions (`SearchReduces`:
polynomial-time instance and answer maps on Cook's Turing machines, correct for every answer).
Since PLS is the class of TFNP problems reducing to LocalOpt (p.17), the first reduction is the
PLS-hardness of Iter and the second its membership in PLS. -/
theorem iter_pls_complete : SearchReduces LocalOpt Iter ∧ SearchReduces Iter LocalOpt := by sorry

end ConstrSOSP
