-- Prove2me | Theorems.Thm_DeReserve_daBT_openFirst
-- name    : DeReserve.daBT_openFirst
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:21:30.271995+00:00
-- url     : https://prove2.me/theorems/58395af2-0d00-429f-b9ac-fe54f7b63e5b
-- title:
--   Proof of Theorem 4 (pp.41–42): DA-BT satisfies open-first (corrected: open-first condition (3))
-- statement:
--   For every capacity profile, priority profile and every $(P,T)$, the DA-BT outcome $\eta$ satisfies open-first at every institution $s$:
--
--   1. $|\{j:(j,o)\in\eta(s)\text{ or }(j,OBC)\in\eta(s)\}|=\min(|\eta(s)|,\,q^o_s+q^{OBC}_s)$;
--   2. if $(i,o)\in\eta(s)$ and $(j,r)\in\eta(s)$ with $r\in\mathcal R$, then $i\succ_s j$;
--   3. (3a) every $(i,c)\in\eta(s)$ such that fewer than $q^o_s+q^{OBC}_s-|\{j:(j,OBC)\in\eta(s)\}|$ members of $\mu_s(\eta)$ have priority over $i$ satisfies $c=o$;
--   4. (3) for every $i$ with $(i,o)\in\eta(s)$ and $t_i=r\in\mathcal R$, the set $\eta'(s)=(\eta(s)\setminus\{(i,o)\})\cup\{(i,r)\}$ has more than $q^r_s$ pairs labelled $r$, or violates (1), (2) or (3a).
--
--   This is clause (4) of the "if" direction of Theorem 4.
--
--   Differences from the source:
--   - correction: open-first (3): for (i, o) ∈ η(s) with t(i) ∈ R, η′(s) = (η(s) \ {(i,o)}) ∪ {(i,t(i))} violates (1) or (2) → open-first adds (3a) (an individual with fewer than q^o_s + q^OBC_s − |{j : (j,OBC) ∈ η(s)}| higher-ranked individuals in μ_s holds an open position) and (3) reads: η′(s) exceeds q^{t(i)}_s or violates (1), (2) or (3a); reason: counterexample: one institution with q_s = (1,0,0,1) and one acceptable OBC applicant who ranks s first; DA-BT gives (i, o), and η′(s) = {(i, OBC)} satisfies (1) and (2), so the printed (3) fails for DA-BT; dropping (3) instead makes labels non-unique (q_s = (0,0,0,1)); (3a) is the extended over-and-above principle stated in prose on p.23
--   - reading: DA step: each individual applies to her top choice / to the best institution that has not rejected her → she applies only to such an institution that is acceptable to her (s P_i ∅), and to none if there is none; reason: p.40: "no individual proposes to an unacceptable institution"; preferences are over S ∪ {∅}
--   - encoding: strict linear orders ≻_s on I ∪ {∅} and P_i on S ∪ {∅}; ∅; membership GC → rank bijections Option I ≃ Fin (|I|+1) and Option S ≃ Fin (|S|+1) (rank 0 best); none; none : Option Res; reason: Lean convention; every strict linear order is such a bijection and conversely, so the instances are the same
--   - encoding: C^BT iterates until no OBC seat is vacant; DA-BT runs until a step has no rejection → C^BT searches the last iteration among q^OBC_s + 1 iterations; DA-BT runs |I|·|S| + 1 steps and a step after a rejection-free step changes nothing; reason: q^OBC strictly decreases at every non-final iteration and every rejecting DA step records a new rejected pair, so the bounds are never reached before termination
-- source:
--   Aygün–Turhan, How to De-reserve Reserves: Admissions to Technical Colleges in India, arXiv:2103.05899v5, Proof of Theorem 4, Open-first, pp.41–42; axiom p.23

import Mathlib
import Definitions.Def_DeReserve_Model

namespace DeReserve

/-- **DA-BT satisfies open-first** (corrected axiom C1). Aygün–Turhan, *How to De-reserve Reserves*, arXiv:2103.05899v5, Proof of Theorem 4,
Open-first, pp.41–42: for every `(P, T)` and every institution `s`, the DA-BT outcome satisfies
open-first conditions (1), (2), the extended over-and-above condition (3a), and the corrected
condition (3). -/
theorem daBT_openFirst {I S : Type*} [Fintype I] [DecidableEq I] [Fintype S] [DecidableEq S]
    (q : S → Cap) (pri : S → Priority I) :
    Mechanism.OpenFirst q pri (daBT q pri) := by sorry

end DeReserve
