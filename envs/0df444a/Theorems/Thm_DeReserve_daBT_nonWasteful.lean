-- Prove2me | Theorems.Thm_DeReserve_daBT_nonWasteful
-- name    : DeReserve.daBT_nonWasteful
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:20:51.945908+00:00
-- url     : https://prove2.me/theorems/fcd3654a-18d3-4cb8-926d-8e690981919b
-- title:
--   Proof of Theorem 4 (p.41): DA-BT is non-wasteful
-- statement:
--   For every capacity profile, priority profile and every $(P,T)$, let $\eta$ be the DA-BT outcome. For every pair $(i,s)$ with $s\,P_i\,\mu_i(\eta)$ and $i\succ_s\emptyset$:
--
--   1. if $t_i\in\mathcal R$, then $|\{j:(j,t_i)\in\eta(s)\}|=q^{t_i}_s$;
--   2. $|\{j:(j,o)\in\eta(s)\text{ or }(j,OBC)\in\eta(s)\}|=q^o_s+q^{OBC}_s$.
--
--   This is clause (3) of the "if" direction of Theorem 4. The second equality accounts for de-reservation: unfilled OBC positions count as open positions.
--
--   Differences from the source:
--   - reading: non-wastefulness: for every (i, s) with s P_i μ(i), all positions i is eligible for at s are exhausted → the two equalities are required for pairs (i, s) with s P_i μ(i) and i ≻_s ∅; reason: p.22 "all positions i is eligible at s"; p.7 defines eligibility through acceptability; under the literal formula DA-BT is wasteful (an unacceptable applicant ranking s first while an open seat is empty)
--   - reading: DA step: each individual applies to her top choice / to the best institution that has not rejected her → she applies only to such an institution that is acceptable to her (s P_i ∅), and to none if there is none; reason: p.40: "no individual proposes to an unacceptable institution"; preferences are over S ∪ {∅}
--   - encoding: strict linear orders ≻_s on I ∪ {∅} and P_i on S ∪ {∅}; ∅; membership GC → rank bijections Option I ≃ Fin (|I|+1) and Option S ≃ Fin (|S|+1) (rank 0 best); none; none : Option Res; reason: Lean convention; every strict linear order is such a bijection and conversely, so the instances are the same
--   - encoding: C^BT iterates until no OBC seat is vacant; DA-BT runs until a step has no rejection → C^BT searches the last iteration among q^OBC_s + 1 iterations; DA-BT runs |I|·|S| + 1 steps and a step after a rejection-free step changes nothing; reason: q^OBC strictly decreases at every non-final iteration and every rejecting DA step records a new rejected pair, so the bounds are never reached before termination
-- source:
--   Aygün–Turhan, How to De-reserve Reserves: Admissions to Technical Colleges in India, arXiv:2103.05899v5, Proof of Theorem 4, Non-wastefulness, p.41; axiom p.22

import Mathlib
import Definitions.Def_DeReserve_Model

namespace DeReserve

/-- **DA-BT is non-wasteful.** Aygün–Turhan, *How to De-reserve Reserves*, arXiv:2103.05899v5, Proof of Theorem 4, Non-wastefulness, p.41: for every
`(P, T)` and every `(i, s)` with `s P_i μ(i)` and `i ≻_s ∅` (reading R1), the reserve positions
of `i`'s category and the `q^o_s + q^OBC_s` open-or-OBC positions at `s` are exhausted. -/
theorem daBT_nonWasteful {I S : Type*} [Fintype I] [DecidableEq I] [Fintype S] [DecidableEq S]
    (q : S → Cap) (pri : S → Priority I) :
    Mechanism.NonWasteful q pri (daBT q pri) := by sorry

end DeReserve
