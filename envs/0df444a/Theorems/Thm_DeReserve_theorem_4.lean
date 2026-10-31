-- Prove2me | Theorems.Thm_DeReserve_theorem_4
-- name    : DeReserve.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:23:26.328615+00:00
-- url     : https://prove2.me/theorems/8c915f85-9406-44e1-ab72-d2cc58f7973f
-- title:
--   Theorem 4 (p.24): characterization of DA-BT (corrected: open-first condition (3) and assignment acceptability)
-- statement:
--   Fix finite sets of individuals $I$ and institutions $S$, a capacity profile $q=(q_s)_{s\in S}$ and a profile of priority orders $(\succ_s)_{s\in S}$. Let $\varphi$ be a mechanism, i.e. a map from preference profiles and reported membership profiles to feasible assignments. Then $\varphi$ satisfies
--
--   1. individual rationality,
--   2. meritocracy,
--   3. non-wastefulness,
--   4. open-first, and
--   5. incentive-compatibility
--
--   if and only if $\varphi$ is the DA-BT mechanism, i.e. $\varphi(P,T)=\mathrm{DA\text{-}BT}(P,T)$ as assignments (institution and category label for every individual) for every preference profile $P$ and every membership profile $T$.
--
--   This is the paper's main result: deferred acceptance under the backward transfers choice rules is the unique mechanism that implements reservations and OBC de-reservations in line with the legal and policy requirements formalized by the five axioms.
--
--   Differences from the source:
--   - correction: open-first (3): for (i, o) ∈ η(s) with t(i) ∈ R, η′(s) = (η(s) \ {(i,o)}) ∪ {(i,t(i))} violates (1) or (2) → open-first adds (3a) (an individual with fewer than q^o_s + q^OBC_s − |{j : (j,OBC) ∈ η(s)}| higher-ranked individuals in μ_s holds an open position) and (3) reads: η′(s) exceeds q^{t(i)}_s or violates (1), (2) or (3a); reason: counterexample: one institution with q_s = (1,0,0,1) and one acceptable OBC applicant who ranks s first; DA-BT gives (i, o), and η′(s) = {(i, OBC)} satisfies (1) and (2), so the printed (3) fails for DA-BT; dropping (3) instead makes labels non-unique (q_s = (0,0,0,1)); (3a) is the extended over-and-above principle stated in prose on p.23
--   - correction: an assignment (p.9) need not respect acceptability → a feasible assignment seats i at s only if i ≻_s ∅; reason: counterexample: one institution with q_s = (1,0,0,0) and one GC applicant with ∅ ≻_s i who ranks s first; the mechanism seating her as (i, o) whenever she reports s acceptable satisfies all five axioms, but DA-BT leaves her unmatched (C^BT chooses only acceptable applicants, p.7)
--   - reading: non-wastefulness: for every (i, s) with s P_i μ(i), all positions i is eligible for at s are exhausted → the two equalities are required for pairs (i, s) with s P_i μ(i) and i ≻_s ∅; reason: p.22 "all positions i is eligible at s"; p.7 defines eligibility through acceptability; under the literal formula DA-BT is wasteful (an unacceptable applicant ranking s first while an open seat is empty)
--   - reading: incentive-compatibility: no deviation (P̃_i, t̃_i) → t̃_i ranges over {t_i, GC}, jointly with any P̃_i; reason: p.7 "Reporting membership to SC, ST, and OBC is optional"; p.44 "no reserve category member can get better of by not revealing"; if a GC applicant could claim OBC, DA-BT would be manipulable (q_s = (0,0,0,1), GC applicants g1 ≻_s g2: claiming OBC gives g2 the seat)
--   - reading: DA step: each individual applies to her top choice / to the best institution that has not rejected her → she applies only to such an institution that is acceptable to her (s P_i ∅), and to none if there is none; reason: p.40: "no individual proposes to an unacceptable institution"; preferences are over S ∪ {∅}
--   - encoding: a mechanism φ : P × T → M (M the set of assignments) → φ : (I → Pref S) → (I → Option Res) → (I → Option (S × Cat)) with the hypothesis that every value is a feasible assignment; reason: the same objects
--   - encoding: strict linear orders ≻_s on I ∪ {∅} and P_i on S ∪ {∅}; ∅; membership GC → rank bijections Option I ≃ Fin (|I|+1) and Option S ≃ Fin (|S|+1) (rank 0 best); none; none : Option Res; reason: Lean convention; every strict linear order is such a bijection and conversely, so the instances are the same
--   - encoding: C^BT iterates until no OBC seat is vacant; DA-BT runs until a step has no rejection → C^BT searches the last iteration among q^OBC_s + 1 iterations; DA-BT runs |I|·|S| + 1 steps and a step after a rejection-free step changes nothing; reason: q^OBC strictly decreases at every non-final iteration and every rejecting DA step records a new rejected pair, so the bounds are never reached before termination
-- source:
--   Aygün–Turhan, How to De-reserve Reserves: Admissions to Technical Colleges in India, arXiv:2103.05899v5, Theorem 4, p.24 (proof pp.40–45); axioms pp.10, 22–23

import Mathlib
import Definitions.Def_DeReserve_Model

namespace DeReserve

/-- **Theorem 4** (corrected: open-first condition (3) and assignment acceptability).
Aygün–Turhan, *How to De-reserve Reserves*, arXiv:2103.05899v5, Theorem 4, p.24 (proof pp.40–45). Fix finite sets of individuals and institutions, a
capacity profile `q` and a profile of priority orders `(≻_s)_{s ∈ S}`. A mechanism `φ` into
feasible assignments satisfies (1) individual rationality, (2) meritocracy,
(3) non-wastefulness, (4) open-first, and (5) incentive-compatibility, if and only if `φ` is
the DA-BT mechanism (equality of assignments, labels included, on the whole domain `P × T`).

**Formalization Note.** Corrections and readings (see the definitions): C1 open-first gains
(3a) and the corrected (3); C2 a feasible assignment seats only acceptable individuals;
R1 non-wastefulness concerns pairs with `i ≻_s ∅`; R2 membership deviations are
`t̃_i ∈ {t_i, GC}`. `i ≻_s j` is `(pri s).higher i j` (smaller rank), `x P_i y` is `P i x < P i y`, `∅` is `none`. -/
theorem theorem_4 {I S : Type*} [Fintype I] [DecidableEq I] [Fintype S] [DecidableEq S]
    (q : S → Cap) (pri : S → Priority I) (φ : Mechanism I S)
    (hφ : ∀ (P : I → Pref S) (T : I → CatMembership), IsAssignment q pri T (φ P T)) :
    (Mechanism.IR φ ∧ Mechanism.Meritocratic pri φ ∧ Mechanism.NonWasteful q pri φ ∧
        Mechanism.OpenFirst q pri φ ∧ Mechanism.IncentiveCompatible φ) ↔
      φ = daBT q pri := by sorry

end DeReserve
