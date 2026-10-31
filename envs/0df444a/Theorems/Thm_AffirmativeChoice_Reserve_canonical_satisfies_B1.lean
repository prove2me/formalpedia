-- Prove2me | Theorems.Thm_AffirmativeChoice_Reserve_canonical_satisfies_B1
-- name    : AffirmativeChoice.Reserve.canonical_satisfies_B1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:34:49.080981+00:00
-- url     : https://prove2.me/theorems/65d626f8-6762-4ca9-be61-d41222c00e8c
-- title:
--   Proof of Theorem 1, Satisfies B1, pp. 20–21 — the reserve of the proof rises by at most one when a top-tier minority becomes a majority
-- statement:
--   Let $q\ge3$ and let $C$ be a substitutable affirmative action rule satisfying MPI and MTC, and let $R_C$ be the reserve function of the proof of Theorem 1 (the largest number of minority students chosen via affirmative action over problems with the same top-tier type configuration). Then $R_C$ satisfies Condition B1: for each problem $(S,\tau,\succ)$, if $\tau'$ is obtained from $\tau$ by changing the type of a top-tier minority student, then
--
--   $$R_C(S,\tau',\succ)=R_C(S,\tau,\succ)\quad\text{or}\quad R_C(S,\tau',\succ)=R_C(S,\tau,\succ)+1.$$
--
--   This is the first of the four bounds that make the representation of Theorem 1 bounded.
-- source:
--   Doğan & Yıldız, Choice with Affirmative Action, SSRN 3626941 (version of October 17, 2021), pp. 20–21, proof of Theorem 1, Satisfies B1

import Mathlib
import Definitions.Def_AffirmativeChoice_Reserve_Model

namespace AffirmativeChoice.Reserve

/-- Proof of Theorem 1, "Satisfies B1", pp. 20–22: for a substitutable affirmative action rule
satisfying MPI and MTC, the reserve function of the proof satisfies Condition B1. -/
theorem canonical_satisfies_B1 {𝒮 : Type*} [Fintype 𝒮] [DecidableEq 𝒮] [Nonempty 𝒮]
    (q : ℕ) (hq : 3 ≤ q) (C : ChoiceRule 𝒮 q)
    (hAA : IsAffirmativeActionRule C) (hsub : Substitutable C)
    (hMPI : MPI C) (hMTC : MTC C) :
    CondB1 q (canonicalReserve C) := by sorry

end AffirmativeChoice.Reserve
