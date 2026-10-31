-- Prove2me | Theorems.Thm_DeReserve_daBT_meritocratic
-- name    : DeReserve.daBT_meritocratic
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:21:05.611916+00:00
-- url     : https://prove2.me/theorems/79256556-0192-422c-b6e8-0bb207d054c9
-- title:
--   Proof of Theorem 4 (pp.40–41): DA-BT complies with meritocracy
-- statement:
--   For every capacity profile, priority profile and every $(P,T)$, let $\eta$ be the DA-BT outcome and $\mu=\mu(\eta)$. For every pair $(i,s)$ with $s\,P_i\,\mu(i)$, and every $j$ with $(j,o)\in\eta(s)$, or with $(j,t_i)\in\eta(s)$ where $t_i\in\mathcal R$,
--
--   $$j\succ_s i.$$
--
--   This is clause (2) of the "if" direction of Theorem 4: cutoffs at every institution are consistent with merit in every category an individual is eligible for.
--
--   Differences from the source:
--   - reading: DA step: each individual applies to her top choice / to the best institution that has not rejected her → she applies only to such an institution that is acceptable to her (s P_i ∅), and to none if there is none; reason: p.40: "no individual proposes to an unacceptable institution"; preferences are over S ∪ {∅}
--   - encoding: strict linear orders ≻_s on I ∪ {∅} and P_i on S ∪ {∅}; ∅; membership GC → rank bijections Option I ≃ Fin (|I|+1) and Option S ≃ Fin (|S|+1) (rank 0 best); none; none : Option Res; reason: Lean convention; every strict linear order is such a bijection and conversely, so the instances are the same
--   - encoding: C^BT iterates until no OBC seat is vacant; DA-BT runs until a step has no rejection → C^BT searches the last iteration among q^OBC_s + 1 iterations; DA-BT runs |I|·|S| + 1 steps and a step after a rejection-free step changes nothing; reason: q^OBC strictly decreases at every non-final iteration and every rejecting DA step records a new rejected pair, so the bounds are never reached before termination
-- source:
--   Aygün–Turhan, How to De-reserve Reserves: Admissions to Technical Colleges in India, arXiv:2103.05899v5, Proof of Theorem 4, Meritocracy, pp.40–41

import Mathlib
import Definitions.Def_DeReserve_Model

namespace DeReserve

/-- **DA-BT complies with meritocracy.** Aygün–Turhan, *How to De-reserve Reserves*, arXiv:2103.05899v5, Proof of Theorem 4, Meritocracy, pp.40–41:
for every `(P, T)` and every `(i, s)` with `s P_i μ(i)`, every `j` holding an open position at
`s`, or a position of `i`'s reserve category, has `j ≻_s i`. -/
theorem daBT_meritocratic {I S : Type*} [Fintype I] [DecidableEq I] [Fintype S] [DecidableEq S]
    (q : S → Cap) (pri : S → Priority I) :
    Mechanism.Meritocratic pri (daBT q pri) := by sorry

end DeReserve
