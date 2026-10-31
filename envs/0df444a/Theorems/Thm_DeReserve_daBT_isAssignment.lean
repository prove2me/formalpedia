-- Prove2me | Theorems.Thm_DeReserve_daBT_isAssignment
-- name    : DeReserve.daBT_isAssignment
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:21:15.328968+00:00
-- url     : https://prove2.me/theorems/9428b3f5-79ae-4152-b38f-aef974705040
-- title:
--   DA-BT outputs a feasible assignment (corrected: assignments seat only acceptable individuals)
-- statement:
--   Fix capacities $q$ and priorities $(\succ_s)_{s\in S}$. For every preference profile $P$ and every reported membership profile $T$, the outcome $\eta$ of the DA-BT mechanism is a feasible assignment:
--
--   1. every seated GC individual holds an open position, and every seated member of $r\in\mathcal R$ holds an open or an $r$ position;
--   2. $|\eta(s)|\le\bar q_s$ and $|\{j:(j,r)\in\eta(s)\}|\le q^r_s$ for every $s$ and every $r\in\mathcal R$;
--   3. every individual seated at $s$ is acceptable at $s$.
--
--   The paper defines a mechanism as a map into assignments (p.10); this statement records that DA-BT is one, which the characterization (Theorem 4) presupposes.
--
--   Differences from the source:
--   - correction: an assignment (p.9) need not respect acceptability → a feasible assignment seats i at s only if i ≻_s ∅; reason: counterexample: one institution with q_s = (1,0,0,0) and one GC applicant with ∅ ≻_s i who ranks s first; the mechanism seating her as (i, o) whenever she reports s acceptable satisfies all five axioms, but DA-BT leaves her unmatched (C^BT chooses only acceptable applicants, p.7)
--   - reading: DA step: each individual applies to her top choice / to the best institution that has not rejected her → she applies only to such an institution that is acceptable to her (s P_i ∅), and to none if there is none; reason: p.40: "no individual proposes to an unacceptable institution"; preferences are over S ∪ {∅}
--   - encoding: strict linear orders ≻_s on I ∪ {∅} and P_i on S ∪ {∅}; ∅; membership GC → rank bijections Option I ≃ Fin (|I|+1) and Option S ≃ Fin (|S|+1) (rank 0 best); none; none : Option Res; reason: Lean convention; every strict linear order is such a bijection and conversely, so the instances are the same
--   - encoding: C^BT iterates until no OBC seat is vacant; DA-BT runs until a step has no rejection → C^BT searches the last iteration among q^OBC_s + 1 iterations; DA-BT runs |I|·|S| + 1 steps and a step after a rejection-free step changes nothing; reason: q^OBC strictly decreases at every non-final iteration and every rejecting DA step records a new rejected pair, so the bounds are never reached before termination
-- source:
--   Aygün–Turhan, How to De-reserve Reserves: Admissions to Technical Colleges in India, arXiv:2103.05899v5, §2.1 Mechanisms p.10 and §4.1 DA-BT pp.20–21

import Mathlib
import Definitions.Def_DeReserve_Model

namespace DeReserve

/-- **DA-BT outputs an assignment.** Aygün–Turhan, *How to De-reserve Reserves*, arXiv:2103.05899v5, §2.1, p.10 ("a mechanism `φ` is a function
`φ : P × T → M`, where `M` denotes the set of all assignments") and §4.1, pp.20–21 (DA-BT).
For every capacity profile `q`, priority profile `≻`, preference profile `P` and membership
profile `T`, the DA-BT outcome is a feasible assignment: labels respect memberships, total and
reserve capacities are respected, and (correction C2) only acceptable individuals are seated.

**Formalization Note.** The DA-BT mechanism is defined by its algorithm (`daBT`), with raw
codomain `I → Option (S × Cat)`; this theorem states that its values are feasible. -/
theorem daBT_isAssignment {I S : Type*} [Fintype I] [DecidableEq I] [Fintype S] [DecidableEq S]
    (q : S → Cap) (pri : S → Priority I) :
    ∀ (P : I → Pref S) (T : I → CatMembership), IsAssignment q pri T (daBT q pri P T) := by sorry

end DeReserve
