-- Prove2me | Theorems.Thm_AffirmativeChoice_Reserve_canonical_satisfies_B3_i
-- name    : AffirmativeChoice.Reserve.canonical_satisfies_B3_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:34:55.490004+00:00
-- url     : https://prove2.me/theorems/fedc4370-2585-46c0-b9ab-cda4d4772757
-- title:
--   Proof of Theorem 1, Satisfies B3-i, p. 21 — the reserve of the proof rises by at most one when a top-tier majority's priority worsens
-- statement:
--   Let $q\ge3$ and let $C$ be a substitutable affirmative action rule satisfying MPI and MTC, with $R_C$ the reserve function of the proof of Theorem 1. Then $R_C$ satisfies Condition B3 (i): for each problem $(S,\tau,\succ')$ and each majority student $M$ in its top tier, if $\succ$ is an improvement over $\succ'$ for $M$, then
--
--   $$R_C(S,\tau,\succ')=R_C(S,\tau,\succ)\quad\text{or}\quad R_C(S,\tau,\succ')=R_C(S,\tau,\succ)+1.$$
--
--   Equivalently, worsening the priority rank of a top-tier majority student within the top tier raises the reserve by at most one.
--
--   **Formalization Note.** $M$ is a top-tier majority at $\succ'$, the ordering in which $M$ has the lower position, so both orderings have the same top-tier set.
-- source:
--   Doğan & Yıldız, Choice with Affirmative Action, SSRN 3626941 (version of October 17, 2021), p. 21, proof of Theorem 1, Satisfies B3-i

import Mathlib
import Definitions.Def_AffirmativeChoice_Reserve_Model

namespace AffirmativeChoice.Reserve

/-- Proof of Theorem 1, "Satisfies B3-i", pp. 20–22: for a substitutable affirmative action rule
satisfying MPI and MTC, the reserve function of the proof satisfies Condition B3 (i). -/
theorem canonical_satisfies_B3_i {𝒮 : Type*} [Fintype 𝒮] [DecidableEq 𝒮] [Nonempty 𝒮]
    (q : ℕ) (hq : 3 ≤ q) (C : ChoiceRule 𝒮 q)
    (hAA : IsAffirmativeActionRule C) (hsub : Substitutable C)
    (hMPI : MPI C) (hMTC : MTC C) :
    CondB3i q (canonicalReserve C) := by sorry

end AffirmativeChoice.Reserve
