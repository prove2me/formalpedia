-- Prove2me | Theorems.Thm_DeReserve_theorem_1
-- name    : DeReserve.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:22:27.31863+00:00
-- url     : https://prove2.me/theorems/d79d4840-ad1b-4692-8fdb-5c0251cf4e2d
-- title:
--   Theorem 1 (p.20): the backward transfers rule complies with the spirit of affirmative action
-- statement:
--   For every institution $s$, every set of individuals $A$, every membership profile $T$ and every individual $i$ with $t_i=r\in\mathcal R$: if $i\notin C^{BT}_s(A)$ when $i$ reports her membership $r$, then $i\notin C^{BT}_s(A)$ when $i$ reports GC (all other reports unchanged).
--
--   That is, $C^{BT}_s$ complies with the spirit of affirmative action (Definition 1): claiming a reserve membership never costs an applicant her seat.
--
--   Differences from the source:
--   - encoding: a choice rule C, and "i reports / does not report her membership to r" → a choice rule depending on the reported membership profile T; not reporting is T updated at i to GC; reason: the BT rule depends on reported memberships (p.18); the same instances
--   - encoding: strict linear orders ≻_s on I ∪ {∅} and P_i on S ∪ {∅}; ∅; membership GC → rank bijections Option I ≃ Fin (|I|+1) and Option S ≃ Fin (|S|+1) (rank 0 best); none; none : Option Res; reason: Lean convention; every strict linear order is such a bijection and conversely, so the instances are the same
--   - encoding: C^BT iterates until no OBC seat is vacant → the last iteration is searched among the first q^OBC_s + 1 iterations; reason: q^OBC strictly decreases at every non-final iteration, so the bound is never reached before termination
-- source:
--   Aygün–Turhan, How to De-reserve Reserves: Admissions to Technical Colleges in India, arXiv:2103.05899v5, Theorem 1, p.20; Definition 1, pp.11–12; proof p.31

import Mathlib
import Definitions.Def_DeReserve_Model

namespace DeReserve

/-- **Theorem 1.** Aygün–Turhan, *How to De-reserve Reserves*, arXiv:2103.05899v5, Theorem 1, p.20 (with Definition 1, pp.11–12): the backward
transfers choice rule complies with the spirit of affirmative action. For every institution
`s`, set `A`, membership profile `T` and member `i` of a reserve category (`t_i = r ∈ R`):
if `i ∉ C^BT_s(A)` when `i` reports `r`, then `i ∉ C^BT_s(A)` when `i` reports `GC`. -/
theorem theorem_1 {I S : Type*} [Fintype I] [DecidableEq I] [Fintype S] [DecidableEq S]
    (q : S → Cap) (pri : S → Priority I) :
    ∀ s : S, CompliesSpiritAA (fun T A => chosenBT (pri s) T (q s) A) := by sorry

end DeReserve
