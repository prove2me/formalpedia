-- Prove2me | Theorems.Thm_DeReserve_daBT_individuallyRational
-- name    : DeReserve.daBT_individuallyRational
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:20:57.398086+00:00
-- url     : https://prove2.me/theorems/d20e0cc0-b192-4803-8196-5744d4232d88
-- title:
--   Proof of Theorem 4 (p.40): DA-BT is individually rational
-- statement:
--   For every capacity profile $q$, priority profile $(\succ_s)_{s\in S}$, preference profile $P$ and membership profile $T$, the DA-BT outcome $\eta$ is individually rational:
--
--   $$\mu_i(\eta)\;R_i\;\emptyset\qquad\text{for every } i\in I.$$
--
--   This is clause (1) of the "if" direction of Theorem 4.
--
--   Differences from the source:
--   - reading: DA step: each individual applies to her top choice / to the best institution that has not rejected her → she applies only to such an institution that is acceptable to her (s P_i ∅), and to none if there is none; reason: p.40: "no individual proposes to an unacceptable institution"; preferences are over S ∪ {∅}
--   - encoding: strict linear orders ≻_s on I ∪ {∅} and P_i on S ∪ {∅}; ∅; membership GC → rank bijections Option I ≃ Fin (|I|+1) and Option S ≃ Fin (|S|+1) (rank 0 best); none; none : Option Res; reason: Lean convention; every strict linear order is such a bijection and conversely, so the instances are the same
--   - encoding: C^BT iterates until no OBC seat is vacant; DA-BT runs until a step has no rejection → C^BT searches the last iteration among q^OBC_s + 1 iterations; DA-BT runs |I|·|S| + 1 steps and a step after a rejection-free step changes nothing; reason: q^OBC strictly decreases at every non-final iteration and every rejecting DA step records a new rejected pair, so the bounds are never reached before termination
-- source:
--   Aygün–Turhan, How to De-reserve Reserves: Admissions to Technical Colleges in India, arXiv:2103.05899v5, Proof of Theorem 4, Individual rationality, p.40

import Mathlib
import Definitions.Def_DeReserve_Model

namespace DeReserve

/-- **DA-BT is individually rational.** Aygün–Turhan, *How to De-reserve Reserves*, arXiv:2103.05899v5, Proof of Theorem 4, Individual rationality,
p.40: for every `(P, T)`, `μ_i(DA-BT(P, T)) R_i ∅` for every individual `i`. -/
theorem daBT_individuallyRational {I S : Type*} [Fintype I] [DecidableEq I] [Fintype S] [DecidableEq S]
    (q : S → Cap) (pri : S → Priority I) :
    Mechanism.IR (daBT q pri) := by sorry

end DeReserve
