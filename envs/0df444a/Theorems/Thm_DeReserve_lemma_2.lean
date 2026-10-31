-- Prove2me | Theorems.Thm_DeReserve_lemma_2
-- name    : DeReserve.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:23:31.268027+00:00
-- url     : https://prove2.me/theorems/2b24da95-9ec2-4926-a7f1-e0e3b2913d5b
-- title:
--   Lemma 2 (p.42): the axioms imply stability with respect to the BT rules (corrected: open-first and acceptability)
-- statement:
--   Let $\varphi$ be a mechanism into feasible assignments that is individually rational, non-wasteful, and satisfies meritocracy and open-first. For every $(P,T)$, let $\eta=\varphi(P,T)$ and $\mu=\mu(\eta)$. Then $\mu$ is stable with respect to the profile of BT choice rules:
--
--   1. $\mu_i\,R_i\,\emptyset$ for every individual $i$;
--   2. $C^{BT}_s(\mu_s,q_s)=\mu_s$ for every institution $s$;
--   3. there is no $(i,s)$ with $s\,P_i\,\mu_i$ and $i\in C^{BT}_s(\mu_s\cup\{i\},q_s)$.
--
--   This is the first half of the "only if" direction of Theorem 4.
--
--   Differences from the source:
--   - correction: open-first (3): for (i, o) ∈ η(s) with t(i) ∈ R, η′(s) = (η(s) \ {(i,o)}) ∪ {(i,t(i))} violates (1) or (2) → open-first adds (3a) (an individual with fewer than q^o_s + q^OBC_s − |{j : (j,OBC) ∈ η(s)}| higher-ranked individuals in μ_s holds an open position) and (3) reads: η′(s) exceeds q^{t(i)}_s or violates (1), (2) or (3a); reason: counterexample: one institution with q_s = (1,0,0,1) and one acceptable OBC applicant who ranks s first; DA-BT gives (i, o), and η′(s) = {(i, OBC)} satisfies (1) and (2), so the printed (3) fails for DA-BT; dropping (3) instead makes labels non-unique (q_s = (0,0,0,1)); (3a) is the extended over-and-above principle stated in prose on p.23
--   - correction: an assignment (p.9) need not respect acceptability → a feasible assignment seats i at s only if i ≻_s ∅; reason: counterexample: one institution with q_s = (1,0,0,0) and one GC applicant with ∅ ≻_s i who ranks s first; the mechanism seating her as (i, o) whenever she reports s acceptable satisfies all five axioms, but DA-BT leaves her unmatched (C^BT chooses only acceptable applicants, p.7)
--   - reading: non-wastefulness: for every (i, s) with s P_i μ(i), all positions i is eligible for at s are exhausted → the two equalities are required for pairs (i, s) with s P_i μ(i) and i ≻_s ∅; reason: p.22 "all positions i is eligible at s"; p.7 defines eligibility through acceptability; under the literal formula DA-BT is wasteful (an unacceptable applicant ranking s first while an open seat is empty)
--   - encoding: a mechanism φ : P × T → M (M the set of assignments) → φ : (I → Pref S) → (I → Option Res) → (I → Option (S × Cat)) with the hypothesis that every value is a feasible assignment; reason: the same objects
--   - encoding: strict linear orders ≻_s on I ∪ {∅} and P_i on S ∪ {∅}; ∅; membership GC → rank bijections Option I ≃ Fin (|I|+1) and Option S ≃ Fin (|S|+1) (rank 0 best); none; none : Option Res; reason: Lean convention; every strict linear order is such a bijection and conversely, so the instances are the same
--   - encoding: C^BT iterates until no OBC seat is vacant → the last iteration is searched among the first q^OBC_s + 1 iterations; reason: q^OBC strictly decreases at every non-final iteration, so the bound is never reached before termination
-- source:
--   Aygün–Turhan, How to De-reserve Reserves: Admissions to Technical Colleges in India, arXiv:2103.05899v5, Lemma 2, p.42 (proof pp.42–44); stability p.37

import Mathlib
import Definitions.Def_DeReserve_Model

namespace DeReserve

/-- **Lemma 2.** Aygün–Turhan, *How to De-reserve Reserves*, arXiv:2103.05899v5, Lemma 2, p.42: if a mechanism `φ` (into feasible assignments) is
individually rational, non-wasteful, and satisfies meritocracy and open-first, then for every
`(P, T)` the matching `μ(φ(P, T))` is stable with respect to the BT choice rules: (1) every
`μ_i R_i ∅`; (2) `C^BT_s(μ_s, q_s) = μ_s` for every `s`; (3) there is no `(i, s)` with
`s P_i μ_i` and `i ∈ C^BT_s(μ_s ∪ {i}, q_s)`. -/
theorem lemma_2 {I S : Type*} [Fintype I] [DecidableEq I] [Fintype S] [DecidableEq S]
    (q : S → Cap) (pri : S → Priority I) (φ : Mechanism I S)
    (hφ : ∀ P T, IsAssignment q pri T (φ P T)) (hIR : Mechanism.IR φ)
    (hNW : Mechanism.NonWasteful q pri φ) (hM : Mechanism.Meritocratic pri φ)
    (hOF : Mechanism.OpenFirst q pri φ) :
    ∀ (P : I → Pref S) (T : I → CatMembership), StableBT q pri P T (muI (φ P T)) := by sorry

end DeReserve
