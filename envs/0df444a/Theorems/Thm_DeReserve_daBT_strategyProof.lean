-- Prove2me | Theorems.Thm_DeReserve_daBT_strategyProof
-- name    : DeReserve.daBT_strategyProof
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:22:10.833686+00:00
-- url     : https://prove2.me/theorems/4f90139c-5133-45ab-8a75-a18d63956603
-- title:
--   Proof of Theorem 3, part (i) (p.36): DA-BT is strategy-proof for a fixed membership profile
-- statement:
--   For every capacity profile and priority profile, every preference profile $P$, every membership profile $T$, every individual $i$ and every preference $\tilde P_i$:
--
--   $$\mu_i\bigl[\mathrm{DA\text{-}BT}(P,T)\bigr]\;R_i\;\mu_i\bigl[\mathrm{DA\text{-}BT}((\tilde P_i,P_{-i}),T)\bigr].$$
--
--   The paper derives it from substitutability and size monotonicity of the $C^{BT}_s$ via Hatfield–Milgrom (2005); it is part (i) of the proof of Theorem 3 and an input of Lemma 3.
--
--   Differences from the source:
--   - reading: DA step: each individual applies to her top choice / to the best institution that has not rejected her → she applies only to such an institution that is acceptable to her (s P_i ∅), and to none if there is none; reason: p.40: "no individual proposes to an unacceptable institution"; preferences are over S ∪ {∅}
--   - encoding: strict linear orders ≻_s on I ∪ {∅} and P_i on S ∪ {∅}; ∅; membership GC → rank bijections Option I ≃ Fin (|I|+1) and Option S ≃ Fin (|S|+1) (rank 0 best); none; none : Option Res; reason: Lean convention; every strict linear order is such a bijection and conversely, so the instances are the same
--   - encoding: C^BT iterates until no OBC seat is vacant; DA-BT runs until a step has no rejection → C^BT searches the last iteration among q^OBC_s + 1 iterations; DA-BT runs |I|·|S| + 1 steps and a step after a rejection-free step changes nothing; reason: q^OBC strictly decreases at every non-final iteration and every rejecting DA step records a new rejected pair, so the bounds are never reached before termination
-- source:
--   Aygün–Turhan, How to De-reserve Reserves: Admissions to Technical Colleges in India, arXiv:2103.05899v5, Proof of Theorem 3, part (i), pp.34 and 36

import Mathlib
import Definitions.Def_DeReserve_Model

namespace DeReserve

/-- **DA-BT is strategy-proof in preferences for a fixed membership profile.** Aygün–Turhan, *How to De-reserve Reserves*, arXiv:2103.05899v5, Proof of
Theorem 3, part (i), p.36 (via Hatfield–Milgrom 2005): for every `(P, T)`, every `i` and every
reported preference `P̃_i`, `μ_i(DA-BT(P, T)) R_i μ_i(DA-BT((P̃_i, P_{-i}), T))`. -/
theorem daBT_strategyProof {I S : Type*} [Fintype I] [DecidableEq I] [Fintype S] [DecidableEq S]
    (q : S → Cap) (pri : S → Priority I) :
    Mechanism.StrategyProof (daBT q pri) := by sorry

end DeReserve
