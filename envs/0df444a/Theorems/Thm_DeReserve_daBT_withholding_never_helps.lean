-- Prove2me | Theorems.Thm_DeReserve_daBT_withholding_never_helps
-- name    : DeReserve.daBT_withholding_never_helps
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:23:10.198934+00:00
-- url     : https://prove2.me/theorems/b1db5c62-bb62-4ff5-8748-7c81eedc321f
-- title:
--   Proof of Theorem 3, part (ii) (p.36): withholding membership never helps under DA-BT
-- statement:
--   For every capacity profile and priority profile, every preference profile $P$, every membership profile $T$ and every individual $i$ with $t_i\in\mathcal R$:
--
--   $$\mu_i\bigl[\mathrm{DA\text{-}BT}(P,T)\bigr]\;R_i\;\mu_i\bigl[\mathrm{DA\text{-}BT}(P,(GC,T_{-i}))\bigr].$$
--
--   The paper obtains it from the improvement property and Afacan (2017, Theorem 2); it is part (ii) of the proof of Theorem 3.
--
--   Differences from the source:
--   - reading: DA step: each individual applies to her top choice / to the best institution that has not rejected her → she applies only to such an institution that is acceptable to her (s P_i ∅), and to none if there is none; reason: p.40: "no individual proposes to an unacceptable institution"; preferences are over S ∪ {∅}
--   - encoding: strict linear orders ≻_s on I ∪ {∅} and P_i on S ∪ {∅}; ∅; membership GC → rank bijections Option I ≃ Fin (|I|+1) and Option S ≃ Fin (|S|+1) (rank 0 best); none; none : Option Res; reason: Lean convention; every strict linear order is such a bijection and conversely, so the instances are the same
--   - encoding: C^BT iterates until no OBC seat is vacant; DA-BT runs until a step has no rejection → C^BT searches the last iteration among q^OBC_s + 1 iterations; DA-BT runs |I|·|S| + 1 steps and a step after a rejection-free step changes nothing; reason: q^OBC strictly decreases at every non-final iteration and every rejecting DA step records a new rejected pair, so the bounds are never reached before termination
-- source:
--   Aygün–Turhan, How to De-reserve Reserves: Admissions to Technical Colleges in India, arXiv:2103.05899v5, Proof of Theorem 3, part (ii), p.36

import Mathlib
import Definitions.Def_DeReserve_Model

namespace DeReserve

/-- **Withholding membership never helps under DA-BT.** Aygün–Turhan, *How to De-reserve Reserves*, arXiv:2103.05899v5, Proof of Theorem 3,
part (ii), p.36 (via Afacan 2017, Theorem 2): for every `(P, T)` and every member `i` of a
reserve category (`t_i = r ∈ R`),
`μ_i(DA-BT(P, T)) R_i μ_i(DA-BT(P, (GC, T_{-i})))`. -/
theorem daBT_withholding_never_helps {I S : Type*} [Fintype I] [DecidableEq I] [Fintype S] [DecidableEq S]
    (q : S → Cap) (pri : S → Priority I) :
    ∀ (P : I → Pref S) (T : I → CatMembership) (i : I) (r : Res), T i = some r →
      P i (muI (daBT q pri P T) i) ≤ P i (muI (daBT q pri P (Function.update T i none)) i) := by sorry

end DeReserve
