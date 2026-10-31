-- Prove2me | Theorems.Thm_DeReserve_labels_determined
-- name    : DeReserve.labels_determined
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:23:20.303995+00:00
-- url     : https://prove2.me/theorems/a88cee9b-5a4a-4e85-8695-fe52c7f398e0
-- title:
--   Proof of Lemma 3 (p.44): open-first determines the category labels (corrected: added by the open-first correction)
-- statement:
--   Let $\eta$ be a feasible assignment, $T$ a membership profile and $s$ an institution such that $\eta$ satisfies (corrected) open-first at $s$ and $C^{BT}_s(\mu_s(\eta),q_s)=\mu_s(\eta)$. Then every $i\in\mu_s(\eta)$ holds at $s$ exactly the category under which $C^{BT}_s(\mu_s(\eta),q_s)$ chooses her:
--
--   $$\eta(i)=(s,c)\quad\text{where } c \text{ is } i\text{'s label in } C^{BT}_s(\mu_s(\eta),q_s).$$
--
--   Lemmas 2 and 3 identify the matching of a mechanism satisfying the axioms with that of DA-BT, while mechanisms output assignments; this statement closes the step "Therefore, $\varphi=$ DA-BT" at the level of assignments.
--
--   Differences from the source:
--   - correction: Therefore, φ = DA−BT (from equality of matchings) → a separate statement that open-first and C^BT_s(μ_s) = μ_s determine every label of η(s); reason: mechanisms output assignments (p.10); under the printed open-first labels are not determined (q_s = (0,0,0,1), one OBC applicant: {(i, OBC)} and {(i, o)} both satisfy the printed axioms), so the step needs corrected open-first (C1) and this statement
--   - correction: open-first (3): for (i, o) ∈ η(s) with t(i) ∈ R, η′(s) = (η(s) \ {(i,o)}) ∪ {(i,t(i))} violates (1) or (2) → open-first adds (3a) (an individual with fewer than q^o_s + q^OBC_s − |{j : (j,OBC) ∈ η(s)}| higher-ranked individuals in μ_s holds an open position) and (3) reads: η′(s) exceeds q^{t(i)}_s or violates (1), (2) or (3a); reason: counterexample: one institution with q_s = (1,0,0,1) and one acceptable OBC applicant who ranks s first; DA-BT gives (i, o), and η′(s) = {(i, OBC)} satisfies (1) and (2), so the printed (3) fails for DA-BT; dropping (3) instead makes labels non-unique (q_s = (0,0,0,1)); (3a) is the extended over-and-above principle stated in prose on p.23
--   - correction: an assignment (p.9) need not respect acceptability → a feasible assignment seats i at s only if i ≻_s ∅; reason: counterexample: one institution with q_s = (1,0,0,0) and one GC applicant with ∅ ≻_s i who ranks s first; the mechanism seating her as (i, o) whenever she reports s acceptable satisfies all five axioms, but DA-BT leaves her unmatched (C^BT chooses only acceptable applicants, p.7)
--   - encoding: strict linear orders ≻_s on I ∪ {∅} and P_i on S ∪ {∅}; ∅; membership GC → rank bijections Option I ≃ Fin (|I|+1) and Option S ≃ Fin (|S|+1) (rank 0 best); none; none : Option Res; reason: Lean convention; every strict linear order is such a bijection and conversely, so the instances are the same
--   - encoding: C^BT iterates until no OBC seat is vacant → the last iteration is searched among the first q^OBC_s + 1 iterations; reason: q^OBC strictly decreases at every non-final iteration, so the bound is never reached before termination
-- source:
--   Aygün–Turhan, How to De-reserve Reserves: Admissions to Technical Colleges in India, arXiv:2103.05899v5, Proof of Lemma 3, p.44 ("Therefore, φ = DA−BT."); open-first p.23

import Mathlib
import Definitions.Def_DeReserve_Model

namespace DeReserve

/-- **Labels are determined by open-first** (added by correction C1). Aygün–Turhan, *How to De-reserve Reserves*, arXiv:2103.05899v5, Proof of Lemma 3,
p.44 ("Therefore, `φ = DA − BT`."): the printed proof equates matchings, while mechanisms
output assignments. Let `η` be a feasible assignment that satisfies (corrected) open-first at
`s` and with `C^BT_s(μ_s(η)) = μ_s(η)`. Then every `i ∈ μ_s(η)` holds in `η(s)` exactly the
category label that `C^BT_s(μ_s(η))` gives her. -/
theorem labels_determined {I S : Type*} [Fintype I] [DecidableEq I] [Fintype S] [DecidableEq S]
    (q : S → Cap) (pri : S → Priority I) :
    ∀ (T : I → CatMembership) (η : Assignment I S) (s : S), IsAssignment q pri T η →
      OpenFirstAt q pri T η s → chosenBT (pri s) T (q s) (muS η s) = muS η s →
      ∀ i ∈ muS η s, η i = (cbt (pri s) T (q s) (muS η s) i).map fun c => (s, c) := by sorry

end DeReserve
