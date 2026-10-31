-- Prove2me | Theorems.Thm_DeReserve_theorem_3
-- name    : DeReserve.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:22:54.529804+00:00
-- url     : https://prove2.me/theorems/fab2fa28-9512-4eae-a3c7-95337c250c40
-- title:
--   Theorem 3 (p.21): DA-BT is incentive-compatible
-- statement:
--   For every capacity profile and priority profile, the DA-BT mechanism is incentive-compatible: for every $(P,T)$, every individual $i$, every preference $\tilde P_i$ and every membership report $\tilde t_i\in\{t_i,GC\}$,
--
--   $$\text{not}\quad \mu_i\bigl[\mathrm{DA\text{-}BT}((\tilde P_i,P_{-i}),(\tilde t_i,T_{-i}))\bigr]\;P_i\;\mu_i\bigl[\mathrm{DA\text{-}BT}(P,T)\bigr].$$
--
--   This is clause (5) of the "if" direction of Theorem 4. Its proof combines strategy-proofness for fixed memberships with the fact that withholding membership never helps.
--
--   Differences from the source:
--   - reading: incentive-compatibility: no deviation (P̃_i, t̃_i) → t̃_i ranges over {t_i, GC}, jointly with any P̃_i; reason: p.7 "Reporting membership to SC, ST, and OBC is optional"; p.44 "no reserve category member can get better of by not revealing"; if a GC applicant could claim OBC, DA-BT would be manipulable (q_s = (0,0,0,1), GC applicants g1 ≻_s g2: claiming OBC gives g2 the seat)
--   - reading: DA step: each individual applies to her top choice / to the best institution that has not rejected her → she applies only to such an institution that is acceptable to her (s P_i ∅), and to none if there is none; reason: p.40: "no individual proposes to an unacceptable institution"; preferences are over S ∪ {∅}
--   - encoding: strict linear orders ≻_s on I ∪ {∅} and P_i on S ∪ {∅}; ∅; membership GC → rank bijections Option I ≃ Fin (|I|+1) and Option S ≃ Fin (|S|+1) (rank 0 best); none; none : Option Res; reason: Lean convention; every strict linear order is such a bijection and conversely, so the instances are the same
--   - encoding: C^BT iterates until no OBC seat is vacant; DA-BT runs until a step has no rejection → C^BT searches the last iteration among q^OBC_s + 1 iterations; DA-BT runs |I|·|S| + 1 steps and a step after a rejection-free step changes nothing; reason: q^OBC strictly decreases at every non-final iteration and every rejecting DA step records a new rejected pair, so the bounds are never reached before termination
-- source:
--   Aygün–Turhan, How to De-reserve Reserves: Admissions to Technical Colleges in India, arXiv:2103.05899v5, Theorem 3, p.21 (proof pp.31–37); incentive-compatibility p.10

import Mathlib
import Definitions.Def_DeReserve_Model

namespace DeReserve

/-- **Theorem 3.** Aygün–Turhan, *How to De-reserve Reserves*, arXiv:2103.05899v5, Theorem 3, p.21: DA-BT is incentive-compatible (reading R2: the
membership report deviates within `{t_i, GC}`, jointly with any preference report). -/
theorem theorem_3 {I S : Type*} [Fintype I] [DecidableEq I] [Fintype S] [DecidableEq S]
    (q : S → Cap) (pri : S → Priority I) :
    Mechanism.IncentiveCompatible (daBT q pri) := by sorry

end DeReserve
