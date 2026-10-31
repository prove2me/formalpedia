-- Prove2me | Theorems.Thm_DeReserve_lemma_3
-- name    : DeReserve.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:23:23.425247+00:00
-- url     : https://prove2.me/theorems/f08c61d0-7f13-4eac-9a37-595e02c42627
-- title:
--   Lemma 3 (p.44): DA-BT is the only stable and strategy-proof mechanism
-- statement:
--   Fix capacities and priorities. A mechanism $\varphi$ is stable with respect to the BT choice rules at every $(P,T)$ and strategy-proof in preferences for every fixed membership profile if and only if its matching coincides with that of DA-BT:
--
--   $$\mu\bigl[\varphi(P,T)\bigr]=\mu\bigl[\mathrm{DA\text{-}BT}(P,T)\bigr]\qquad\text{for every }(P,T).$$
--
--   The paper derives it from Hatfield, Kominers and Westkamp (2021, Theorem 4); it is the second half of the "only if" direction of Theorem 4.
--
--   Differences from the source:
--   - reading: "the DA-BT mechanism is the only mechanism that is stable and strategy-proof" → a mechanism φ is stable at every (P, T) and strategy-proof iff μ(φ(P,T)) = μ(DA-BT(P,T)) for every (P, T); reason: stability and strategy-proofness depend only on the induced matching, and the proof (p.44) uses the lemma to identify matchings
--   - generalization: a mechanism maps profiles to assignments (p.10) → φ is any map from profiles to I → Option (S × Cat), with no feasibility hypothesis; reason: stability and strategy-proofness read only the induced matching, so the statement covers every mechanism of the source, whose assignments are such maps
--   - reading: DA step: each individual applies to her top choice / to the best institution that has not rejected her → she applies only to such an institution that is acceptable to her (s P_i ∅), and to none if there is none; reason: p.40: "no individual proposes to an unacceptable institution"; preferences are over S ∪ {∅}
--   - encoding: strict linear orders ≻_s on I ∪ {∅} and P_i on S ∪ {∅}; ∅; membership GC → rank bijections Option I ≃ Fin (|I|+1) and Option S ≃ Fin (|S|+1) (rank 0 best); none; none : Option Res; reason: Lean convention; every strict linear order is such a bijection and conversely, so the instances are the same
--   - encoding: C^BT iterates until no OBC seat is vacant; DA-BT runs until a step has no rejection → C^BT searches the last iteration among q^OBC_s + 1 iterations; DA-BT runs |I|·|S| + 1 steps and a step after a rejection-free step changes nothing; reason: q^OBC strictly decreases at every non-final iteration and every rejecting DA step records a new rejected pair, so the bounds are never reached before termination
-- source:
--   Aygün–Turhan, How to De-reserve Reserves: Admissions to Technical Colleges in India, arXiv:2103.05899v5, Lemma 3, p.44

import Mathlib
import Definitions.Def_DeReserve_Model

namespace DeReserve

/-- **Lemma 3.** Aygün–Turhan, *How to De-reserve Reserves*, arXiv:2103.05899v5, Lemma 3, p.44: the DA-BT mechanism is the only mechanism that is
stable (with respect to the BT choice rules, at every `(P, T)`) and strategy-proof (in
preferences, for every fixed membership profile). Stated at the level of matchings: a mechanism
`φ` is stable and strategy-proof iff `μ(φ(P, T)) = μ(DA-BT(P, T))` for every `(P, T)`.

**Formalization Note.** Stability and strategy-proofness depend only on the induced matching,
so the statement compares matchings; labels are handled by `labels_determined`. -/
theorem lemma_3 {I S : Type*} [Fintype I] [DecidableEq I] [Fintype S] [DecidableEq S]
    (q : S → Cap) (pri : S → Priority I) (φ : Mechanism I S) :
    ((∀ (P : I → Pref S) (T : I → CatMembership), StableBT q pri P T (muI (φ P T))) ∧
        Mechanism.StrategyProof φ) ↔
      ∀ (P : I → Pref S) (T : I → CatMembership), muI (φ P T) = muI (daBT q pri P T) := by sorry

end DeReserve
