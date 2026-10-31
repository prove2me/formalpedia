-- Prove2me | Theorems.Thm_AffirmativeChoice_Reserve_canonical_satisfies_B2
-- name    : AffirmativeChoice.Reserve.canonical_satisfies_B2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:34:57.511164+00:00
-- url     : https://prove2.me/theorems/1b3f75fc-3c1c-4b57-8ed4-6d26559cb3b0
-- title:
--   Proof of Theorem 1, Satisfies B2, p. 21 — the reserve of the proof rises by at most one when a top-tier minority's priority improves
-- statement:
--   Let $q\ge3$ and let $C$ be a substitutable affirmative action rule satisfying MPI and MTC, with $R_C$ the reserve function of the proof of Theorem 1. Then $R_C$ satisfies Condition B2: for each problem $(S,\tau,\succ)$, if $\succ'$ is an improvement over $\succ$ for a top-tier minority student, then
--
--   $$R_C(S,\tau,\succ')=R_C(S,\tau,\succ)\quad\text{or}\quad R_C(S,\tau,\succ')=R_C(S,\tau,\succ)+1.$$
--
--   **Formalization Note.** The improved student is a top-tier minority at $\succ$; an improvement of a top-tier student leaves the top-tier set unchanged.
-- source:
--   Doğan & Yıldız, Choice with Affirmative Action, SSRN 3626941 (version of October 17, 2021), p. 21, proof of Theorem 1, Satisfies B2

import Mathlib
import Definitions.Def_AffirmativeChoice_Reserve_Model

namespace AffirmativeChoice.Reserve

/-- Proof of Theorem 1, "Satisfies B2", pp. 20–22: for a substitutable affirmative action rule
satisfying MPI and MTC, the reserve function of the proof satisfies Condition B2. -/
theorem canonical_satisfies_B2 {𝒮 : Type*} [Fintype 𝒮] [DecidableEq 𝒮] [Nonempty 𝒮]
    (q : ℕ) (hq : 3 ≤ q) (C : ChoiceRule 𝒮 q)
    (hAA : IsAffirmativeActionRule C) (hsub : Substitutable C)
    (hMPI : MPI C) (hMTC : MTC C) :
    CondB2 q (canonicalReserve C) := by sorry

end AffirmativeChoice.Reserve
